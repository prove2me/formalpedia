-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch237
-- name    : Polychromatic418967fa_Branch237
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:28:16.918659+00:00
-- url     : https://prove2.me/theorems/ad53747a-5ea0-4aca-9d6a-4e6682fcdde9
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch237_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_237 : allB 237 237 :=
  allB_succ' 2 236 237 (Eq.refl Bool.true) (allA_succ_of_accept 1 236 237 (accept_3_4 1 236 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 236 237)) (allB_succ' 3 235 237 (Eq.refl Bool.true) (allA_succ_of_accept 2 235 237
  (accept_3_5 2 235 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 235 237
  (Polychromatic418967fa.accept_29_1_3_5_1_14192 1 235 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 235 237))) (allB_succ' 4 234 237 (Eq.refl Bool.true) (allA_succ_of_gcd 3 234 237 3 1 78 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 234 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 234 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 234 237 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 234 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 234 237)))) (allB_succ' 5 233 237 (Eq.refl Bool.true) (allA_succ_of_accept 4
  233 237 (accept_3_4 4 233 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 233 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 233 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 233 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 233 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 233 237 (accept_3_4 1 233 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 233 237))))) (allB_succ' 6 232 237 (Eq.refl Bool.true) (allA_succ_of_accept 5 232 237
  (accept_3_5 5 232 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 232 237
  (Polychromatic418967fa.accept_9_4_7_3_1_43 4 232 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 232 237 (Polychromatic418967fa.accept_15_3_7_12_1_372 3 232 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 232 237 (accept_3_5 2 232 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 232 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 232 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 232 237)))))) (allB_succ' 7 231 237 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 231 237 3 2 77 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 231 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 231 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 231 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 231 237 3 1 77 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 231 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 231 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 231 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 231 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 231 237))))))) (allB_succ' 8 230 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 230 237 (accept_3_4 7 230 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  230 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 230 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 230 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 230 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 230 237 (accept_3_4 4 230 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 230 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 230 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 230 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 230 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 230 237 (accept_3_4 1 230 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230
  237)))))))) (allB_succ' 9 229 237 (Eq.refl Bool.true) (allA_succ_of_accept 8 229 237 (accept_3_5 8 229 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 229 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 229 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 229 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 229 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 229 237 (accept_3_5 5 229 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  229 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 229 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 229 237 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 229 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 229 237 (accept_3_5 2 229 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 229 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 229 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 229 237))))))))) (allB_succ' 10 228 237 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 228 237 3 3 76 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 228 237 (Polychromatic418967fa.accept_13_8_7_3_1_430 8 228 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 228 237 (Polychromatic418967fa.accept_15_7_3_12_1_365
  7 228 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 228 237 3 2 76 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 228 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 228 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 228 237 (Polychromatic418967fa.accept_13_4_7_3_1_92 4 228 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 228 237 3 1 76 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 228 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 228 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 228 237
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 228 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 228 237)))))))))) (allB_succ' 11 227 237 (Eq.refl Bool.true) (allA_succ_of_accept 10 227 237 (accept_3_4 10
  227 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 227 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 227 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 227 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 227 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 237 (accept_3_4 7 227 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 227 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 227 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 227 237 (Polychromatic418967fa.accept_9_5_2_3_1_194 5
  227 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 227 237 (accept_3_4 4 227
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 227 237
  (Polychromatic418967fa.accept_12_3_11_9_1_193 3 227 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 227 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 227 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 237 (accept_3_4 1 227 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 227 237))))))))))) (allB_succ' 12 226 237 (Eq.refl Bool.true) (allA_succ_of_accept 11 226 237
  (accept_3_5 11 226 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 226 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 226 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 226 237 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 226 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 226 237 (accept_3_5 8 226 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 226 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 226 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 226 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 6
  226 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 226 237 (accept_3_5 5 226
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 226 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 226 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 226 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 226 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 226 237 (accept_3_5 2 226 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 226 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 226 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 226 237)))))))))))) (allB_succ' 13 225 237 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 225 237 3 4 75 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 225 237 (Polychromatic418967fa.accept_20_11_5_17_1_5490 11 225 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 237
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 225 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 225 237 3 3 75 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 225 237 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 225 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 237 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 225 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 225 237 3 2 75 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 225 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 225 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 225 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 225 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 225 237 3 1 75 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 225 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 225 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 237
  (Polychromatic418967fa.accept_11_1_5_6_1_397 1 225 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 225 237))))))))))))) (allB_succ' 14 224 237 (Eq.refl Bool.true) (allA_succ_of_accept 13 224 237 (accept_3_4
  13 224 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 224 237
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 224 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 224 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 224 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 224 237 (accept_3_4 10 224 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 224 237 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 224 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 224 237
  (Polychromatic418967fa.accept_21_8_14_6_1_9800 8 224 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 224 237 (accept_3_4 7 224 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  224 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 224 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 224 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 224 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 224 237 (accept_3_4 4 224 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 224 237 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 224 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 224 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 224 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 224 237 (accept_3_4 1 224 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224
  237)))))))))))))) (allB_succ' 15 223 237 (Eq.refl Bool.true) (allA_succ_of_accept 14 223 237 (accept_3_5 14 223 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 223 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 13
  223 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 223 237
  (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 223 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 223 237 (accept_3_5 11 223 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 223 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 223 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 223 237 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 223 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 223 237 (accept_3_5 8 223 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 223 237 (Polychromatic418967fa.accept_21_7_13_6_1_349 7 223 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 223 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 223 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 223 237 (accept_3_5 5 223 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  223 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 223 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 223 237 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 223 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 237 (accept_3_5 2 223 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 223 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 223 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 223 237))))))))))))))) (allB_succ' 16 222 237 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 222 237 3 5 74 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 222 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 222 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 222 237 (Polychromatic418967fa.accept_9_4_6_3_1_179
  13 222 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 222 237 3 4 74 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 222 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 222 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 222 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 222 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 222 237 3 3 74 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 222 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 222 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 222 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 222 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 237 3 2 74 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 222 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 222 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 222 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 222 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 222 237 3 1 74 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 222 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 222 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 222 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 222 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 222 237)))))))))))))))) (allB_succ' 17 221 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 221 237 (accept_3_4 16 221 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 221 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 221 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 221 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 221 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 221 237 (accept_3_4 13 221 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 221 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 221 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 221 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 221 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 221 237 (accept_3_4 10 221 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  221 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 221 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 221 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 221 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 221 237 (accept_3_4 7 221 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 221 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 221 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 221 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 221 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 221 237 (accept_3_4 4 221 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  221 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 221 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 221 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 221 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 221 237 (accept_3_4 1 221 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 221 237))))))))))))))))) (allB_succ' 18 220 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 220 237 (accept_3_5 17 220 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 220 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 220 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 220 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 220 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 220 237 (accept_3_5 14 220 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 220 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 220 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 220 237
  (Polychromatic418967fa.accept_21_12_10_6_1_1191 12 220 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 220 237 (accept_3_5 11 220 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 220 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 220 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 220 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 220 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 220 237 (accept_3_5 8 220 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 220 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 7
  220 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 220 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 220 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 220 237 (accept_3_5 5 220 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  220 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 220 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 220 237 (Polychromatic418967fa.accept_14_3_10_13_1_339 3 220 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 220 237 (accept_3_5 2 220 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 220 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 220 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220 237)))))))))))))))))) (allB_succ' 19 219
  237 (Eq.refl Bool.true) (allA_succ_of_gcd 18 219 237 3 6 73 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 219 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 219 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 237
  (Polychromatic418967fa.accept_11_5_10_6_1_793 16 219 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 219 237 3 5 73 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 219 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 219 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 219
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 219 237 3 4 73 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 219 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 219 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 219 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 219 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 219 237 3 3 73 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 219 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 219 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 237
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 219 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 219 237 3 2 73 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 219 237 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 219 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 219 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 219 237 3 1 73 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 219 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 219 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 219 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 219 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 219 237))))))))))))))))))) (allB_succ' 20 218 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 218 237 (accept_3_4 19 218 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 218 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 218 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 218 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 218 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 218 237 (accept_3_4 16 218 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 218 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 218 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 218 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 218 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 218 237 (accept_3_4 13 218 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 218 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 218 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 218 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 218 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 218 237 (accept_3_4 10 218 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 218 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 218 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 218 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 218 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 218 237 (accept_3_4 7 218 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  218 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 218 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 218 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 218 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 218 237 (accept_3_4 4 218 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 218 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 218 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 218 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 218 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 218 237 (accept_3_4 1 218 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  237)))))))))))))))))))) (allB_succ' 21 217 237 (Eq.refl Bool.true) (allA_succ_of_accept 20 217 237 (accept_3_5 20 217
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 217 237
  (Polychromatic418967fa.accept_13_6_9_3_1_915 19 217 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 217 237 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 217 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 217 237 (accept_3_5 17 217 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 217 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 217 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 217 237 (Polychromatic418967fa.accept_9_6_1_3_1_191
  15 217 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 217 237 (accept_3_5 14
  217 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 217 237
  (Polychromatic418967fa.accept_9_4_1_3_1_190 13 217 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 217 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 217 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 217 237 (accept_3_5 11 217 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 217 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 217 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 217 237
  (Polychromatic418967fa.accept_17_9_13_16_1_3266 9 217 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 217 237 (accept_3_5 8 217 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  217 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 217 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 217 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 217 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 217 237 (accept_3_5 5 217 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 217 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 217 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 217 237
  (Polychromatic418967fa.accept_11_3_8_6_1_788 3 217 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 217 237 (accept_3_5 2 217 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  217 237 (Polychromatic418967fa.accept_14_1_7_13_1_333 1 217 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 217 237))))))))))))))))))))) (allB_succ' 22 216 237 (Eq.refl Bool.true) (allA_succ_of_gcd 21 216
  237 3 7 72 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  216 237 (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 216 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 216 237 (Polychromatic418967fa.accept_14_5_6_13_1_3145 19 216 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 216 237 3 6 72 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 216 237
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 216 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 216 237 (Polychromatic418967fa.accept_19_16_7_9_1_7321 16 216 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 216 237 3 5 72 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 216 237
  (Polychromatic418967fa.accept_35_14_6_27_1_14191 14 216 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 216 237 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 216 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 216 237 3 4 72 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 216 237
  (Polychromatic418967fa.accept_10_1_6_7_1_710 11 216 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 216 237 (Polychromatic418967fa.accept_15_10_6_12_1_1645 10 216 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 216 237 3 3 72 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 216 237 (Polychromatic418967fa.accept_19_8_7_9_1_10251
  8 216 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 216 237
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 216 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 216 237 3 2 72 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 216 237 (Polychromatic418967fa.accept_13_5_8_3_1_1535 5 216 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 216 237 (Polychromatic418967fa.accept_16_4_8_13_1_1059 4 216
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 216 237 3 1 72 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 216 237
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 2 216 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 216 237 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 216 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 216 237)))))))))))))))))))))) (allB_succ' 23 215 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 22 215 237 (accept_3_4 22 215 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 215 237 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 215 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 215 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 215 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 215 237 (accept_3_4 19 215 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 215 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 237
  (Polychromatic418967fa.accept_13_4_7_3_1_92 17 215 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 215 237 (accept_3_4 16 215 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 215 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 215 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 215 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 215 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 237 (accept_3_4 13 215 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 215 237 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 215 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 215 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 215 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 215 237 (accept_3_4 10 215 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  215 237 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 215 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 215 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 215 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 237 (accept_3_4 7 215 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 215 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 215 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 215 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 215 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 215 237 (accept_3_4 4 215 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  215 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 215 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 215 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 215 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 237 (accept_3_4 1 215 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 215 237))))))))))))))))))))))) (allB_succ' 24 214 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 214 237 (accept_3_5 23 214 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 214 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 214 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 214 237 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 214 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 214 237 (accept_3_5 20 214 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 214 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 214 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 214 237
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 214 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 214 237 (accept_3_5 17 214 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 214 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 214 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 214 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 214 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 214 237 (accept_3_5 14 214 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 214 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 214 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 214 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 214 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 214 237 (accept_3_5 11 214 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 214 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 214 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 214 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 214 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 214 237 (accept_3_5 8 214 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 214 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 214 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 214 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 214 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 214 237 (accept_3_5 5 214 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  214 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 214 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 214 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 214 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 214 237 (accept_3_5 2 214 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 214 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 214 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 214 237)))))))))))))))))))))))) (allB_succ' 25 213 237
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 213 237 3 8 71 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 213 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 213 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 213 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 213 237 3 7 71 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 213 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 213 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 213 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 213 237 3 6 71 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 213 237
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 213 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 213 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 213 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 213 237 3 5 71 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 213 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 14
  213 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 213 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 213 237 3 4 71 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 213 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 213 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 213 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 213 237 3 3 71 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 213 237
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 213 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 213 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 213 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 213 237 3 2 71 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 213 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 213 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 4 213 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 213 237 3 1 71 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 213 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 213 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 213 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213 237))))))))))))))))))))))))) (allB_succ' 26
  212 237 (Eq.refl Bool.true) (allA_succ_of_accept 25 212 237 (accept_3_4 25 212 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 212 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 212 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 212 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 23
  212 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 212 237 (accept_3_4 22
  212 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 212 237
  (Polychromatic418967fa.accept_15_6_2_12_1_885 21 212 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 212 237 (Polychromatic418967fa.accept_9_2_5_3_1_37 20 212 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 212 237 (accept_3_4 19 212 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 212 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 212 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 212 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17
  212 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 212 237 (accept_3_4 16
  212 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 212 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 212 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 212 237 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 212 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 212 237 (accept_3_4 13 212 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 212 237 (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 212 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 212 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 212 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 212 237 (accept_3_4 10 212 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  212 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 212 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 212 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 212 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 212 237 (accept_3_4 7 212 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 212 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 212 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 212 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 212 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 212 237 (accept_3_4 4 212 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  212 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 212 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 212 237 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 212 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 212 237 (accept_3_4 1 212 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 212 237)))))))))))))))))))))))))) (allB_succ' 27 211 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 211 237 (accept_3_5 26 211 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 211 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 211 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 211 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 211 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 211 237 (accept_3_5 23 211 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 211 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 211 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 211 237
  (Polychromatic418967fa.accept_14_7_1_13_1_357 21 211 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 211 237 (accept_3_5 20 211 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 211 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 211 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 211 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 211 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 211 237 (accept_3_5 17 211 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 211 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 211 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 211 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 211 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 211 237 (accept_3_5 14 211 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 211 237 (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 211 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 211 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 211 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 211 237 (accept_3_5 11 211 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 211 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 211 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 211 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 211 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 211 237 (accept_3_5 8 211 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  211 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 211 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 211 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 211 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 211 237 (accept_3_5 5 211 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 211 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 211 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 211 237
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 211 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 211 237 (accept_3_5 2 211 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  211 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 211 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 211 237))))))))))))))))))))))))))) (allB_succ' 28 210 237 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 210 237 3 9 70 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 210 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 210 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 210 237 (Polychromatic418967fa.accept_13_12_2_3_1_1527 25 210
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 210 237 3 8 70 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 210 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 210 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 210 237 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 210 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 210 237 3 7 70 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 210 237 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  20 210 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 210 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 210 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 210 237 3 6 70 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 210 237 (Polychromatic418967fa.accept_19_17_1_9_1_4595 17 210 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 210 237 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 210
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 210 237 3 5 70 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 210 237
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 210 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 210 237 (Polychromatic418967fa.accept_18_13_12_3_1_3857 13 210 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 210 237 3 4 70 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 210 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 210 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 210 237 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 210 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 210 237 3 3 70 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 210 237 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 210 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 210 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 210 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 237 3 2 70 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 210 237 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 210 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 210 237 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 210 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 210 237 3 1 70 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 210 237
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 210 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 210 237 (Polychromatic418967fa.accept_13_1_2_3_1_911 1 210 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 210 237)))))))))))))))))))))))))))) (allB_succ' 29 209 237 (Eq.refl
  Bool.true) (allA_succ_of_accept 28 209 237 (accept_3_4 28 209 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 209 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 209 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 209 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 209 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 209 237 (accept_3_4 25 209 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 209 237 (Polychromatic418967fa.accept_9_6_2_3_1_771
  24 209 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 209 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 209 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 209 237 (accept_3_4 22 209 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 209 237 (Polychromatic418967fa.accept_16_5_1_13_1_1053 21 209 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 209 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 209 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 209 237 (accept_3_4 19 209 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 209 237 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 209 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 209 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 209 237 (accept_3_4 16 209 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 209 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 209 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 209 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 209 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 237 (accept_3_4 13 209 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 209 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 209 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 209 237
  (Polychromatic418967fa.accept_13_11_1_3_1_910 11 209 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 209 237 (accept_3_4 10 209 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  209 237 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 209 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 209 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 209 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 237 (accept_3_4 7 209 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 209 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 209 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 209 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 209 237 (accept_3_4 4 209 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  209 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 209 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 209 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 209 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 237 (accept_3_4 1 209 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 209 237))))))))))))))))))))))))))))) (allB_succ' 30 208 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 208 237 (accept_3_5 29 208 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 208 237 (Polychromatic418967fa.accept_22_6_10_17_1_14190 28 208 237 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 208 237 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 208 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 208 237 (accept_3_5 26 208 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 208 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 208 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 208 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 208 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 208 237 (accept_3_5 23 208 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 208 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 208 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 208 237 (Polychromatic418967fa.accept_19_2_18_9_1_8829 21 208 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 208 237 (accept_3_5 20 208 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 208 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 208 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 208 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 208 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 208 237 (accept_3_5 17 208 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 208 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 208 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 208 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 208 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 208 237 (accept_3_5 14 208 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 208 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 208 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 208 237
  (Polychromatic418967fa.accept_19_12_18_9_1_7352 12 208 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 208 237 (accept_3_5 11 208 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 208 237 (Polychromatic418967fa.accept_15_10_13_12_1_3384 10 208 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 208 237 (Polychromatic418967fa.accept_10_9_8_7_1_714 9
  208 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 208 237 (accept_3_5 8 208
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 208 237 (Polychromatic418967fa.accept_6_1_4_3_1_14
  7 208 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 208 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 208 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 208 237 (accept_3_5 5 208 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  208 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 208 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 208 237 (Polychromatic418967fa.accept_15_3_13_12_1_348 3 208 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 208 237 (accept_3_5 2 208 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 208 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 208 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208 237))))))))))))))))))))))))))))))
  (allB_succ' 31 207 237 (Eq.refl Bool.true) (allA_succ_of_gcd 30 207 237 3 10 69 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 207 237
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 207 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 207 237 (Polychromatic418967fa.accept_13_2_12_3_1_415 28 207 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 207 237 3 9 69 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 207 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26
  207 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 237
  (Polychromatic418967fa.accept_11_3_9_6_1_105 25 207 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 207 237 3 8 69 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 207 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 207 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 207 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 207 237 3 7 69 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 207 237
  (Polychromatic418967fa.accept_18_2_9_3_1_3825 20 207 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 207 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 207 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 207 237 3 6 69 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 207 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 17
  207 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 207 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 207 237 3 5 69 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 207 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 207 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 207
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 207 237 3 4 69 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 207 237
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 207 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 207 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 207 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 207 237 3 3 69 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 207 237 (Polychromatic418967fa.accept_18_8_9_3_1_2645 8 207 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 237
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 207 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 207 237 3 2 69 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 207 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 207 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 237 (Polychromatic418967fa.accept_13_4_12_3_1_2999 4 207
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 207 237 3 1 69 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 207 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 207 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 207 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 207 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 207 237))))))))))))))))))))))))))))))) (allB_succ' 32 206 237 (Eq.refl
  Bool.true) (allA_succ_of_accept 31 206 237 (accept_3_4 31 206 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 206 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 206 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 206 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 206 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 206 237 (accept_3_4 28 206 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 206 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  206 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 206 237
  (Polychromatic418967fa.accept_16_10_14_13_1_1870 26 206 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 206 237 (accept_3_4 25 206 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 206 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 206 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 206 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 206 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 206 237 (accept_3_4 22 206 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 206 237 (Polychromatic418967fa.accept_10_1_6_7_1_710
  21 206 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 206 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 206 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 206 237 (accept_3_4 19 206 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 206 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 206 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 206 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 206 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 206 237 (accept_3_4 16 206 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 206 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 206 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 206 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 206 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 206 237 (accept_3_4 13 206 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 206 237 (Polychromatic418967fa.accept_18_12_8_3_1_1627 12 206 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 206 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 206 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 206 237 (accept_3_4 10 206 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 206 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 206 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 206 237
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 8 206 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 206 237 (accept_3_4 7 206 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  206 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 206 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 206 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 206 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 206 237 (accept_3_4 4 206 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 206 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 206 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 206 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 206 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 206 237 (accept_3_4 1 206 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  237)))))))))))))))))))))))))))))))) (allB_succ' 33 205 237 (Eq.refl Bool.true) (allA_succ_of_accept 32 205 237
  (accept_3_5 32 205 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 205 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 205 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 205 237 (Polychromatic418967fa.accept_18_12_7_3_1_2666 30 205 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 205 237 (accept_3_5 29 205 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 205 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 205 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 205 237 (Polychromatic418967fa.accept_12_3_1_9_1_202
  27 205 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 205 237 (accept_3_5 26
  205 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 205 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 205 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 205 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 205 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 205 237 (accept_3_5 23 205 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 205 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 205 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 205 237
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 21 205 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 205 237 (accept_3_5 20 205 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 205 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 205 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 205 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 205 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 237 (accept_3_5 17 205 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 205 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  205 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 205 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 205 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 205 237 (accept_3_5 14 205 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 205 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 205 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 205 237 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 205 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 237 (accept_3_5 11 205 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 205 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 205 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 205 237
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 205 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 205 237 (accept_3_5 8 205 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  205 237 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 205 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 205 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 205 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 205 237 (accept_3_5 5 205 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 205 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 205 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 205 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 205 237 (accept_3_5 2 205 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  205 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 205 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 205 237))))))))))))))))))))))))))))))))) (allB_succ' 34 204 237 (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 204 237 3 11 68 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 204 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 204 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 204 237 (Polychromatic418967fa.accept_9_4_6_3_1_179
  31 204 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 204 237 3 10 68 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 204 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 204 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 204 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 204 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 204 237 3 9 68 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 204 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 26
  204 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 204 237
  (Polychromatic418967fa.accept_8_1_4_5_1_48 25 204 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 204 237 3 8 68 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 204 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 204 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 204 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 204 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 204 237 3 7 68 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 204 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 204 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 204 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 204 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 204 237 3 6 68 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 204 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 17
  204 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 204 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 204 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 204 237 3 5 68 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 204 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 204 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 204 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 204 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 204 237 3 4 68 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 204 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 204 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 204 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 204 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 204 237 3 3 68 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 204 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 204 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 204 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 204 237 3 2 68 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 204 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 204 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 204 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 204 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 204 237 3 1 68 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 204 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 204 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 204 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 204 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 204 237)))))))))))))))))))))))))))))))))) (allB_succ' 35 203 237 (Eq.refl
  Bool.true) (allA_succ_of_accept 34 203 237 (accept_3_4 34 203 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 203 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 203 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 203 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 203 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 203 237 (accept_3_4 31 203 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 203 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  203 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 203 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 203 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 203 237 (accept_3_4 28 203 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 203 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 203 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 203 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 203 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 237 (accept_3_4 25 203 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 203 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 203 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 237
  (Polychromatic418967fa.accept_11_1_5_6_1_397 23 203 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 203 237 (accept_3_4 22 203 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 203 237 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 203 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 203 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 203 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 237 (accept_3_4 19 203 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 203 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 203 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 203 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 203 237 (accept_3_4 16 203 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 203 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 203 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 203 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 203 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 237 (accept_3_4 13 203 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 237 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 203 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 203 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 203 237 (accept_3_4 10 203 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  203 237 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 203 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 203 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 203 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 237 (accept_3_4 7 203 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 203 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 237
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 203 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 203 237 (accept_3_4 4 203 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  203 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 203 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 203 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 203 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 237 (accept_3_4 1 203 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 203 237))))))))))))))))))))))))))))))))))) (allB_succ' 36 202 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 202 237 (accept_3_5 35 202 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 202 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 202 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 202 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 202 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 202 237 (accept_3_5 32 202 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 202 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 202 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 202 237
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 202 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 202 237 (accept_3_5 29 202 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 202 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 202 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 202 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 202 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 202 237 (accept_3_5 26 202 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 202 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 202 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 202 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 202 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 202 237 (accept_3_5 23 202 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 202 237 (Polychromatic418967fa.accept_13_9_7_3_1_1531 22 202 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 202 237 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 202 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 202 237 (accept_3_5 20 202 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 202 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 202 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 202 237
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 202 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 202 237 (accept_3_5 17 202 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 202 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 202 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 202 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 202 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 202 237 (accept_3_5 14 202 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 202 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 202 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 202 237
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 202 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 202 237 (accept_3_5 11 202 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 202 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 202 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 202 237 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 202 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 202 237 (accept_3_5 8 202 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 202 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7
  202 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 202 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 202 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 202 237 (accept_3_5 5 202 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  202 237 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 202 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 202 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 202 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 202 237 (accept_3_5 2 202 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 202 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 202 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 202 237)))))))))))))))))))))))))))))))))))) (allB_succ'
  37 201 237 (Eq.refl Bool.true) (allA_succ_of_gcd 36 201 237 3 12 67 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 201 237 (Polychromatic418967fa.accept_13_9_6_3_1_1514
  35 201 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 237
  (Polychromatic418967fa.accept_10_4_1_7_1_371 34 201 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 201 237 3 11 67 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 201 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 201 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 237 (Polychromatic418967fa.accept_11_9_3_6_1_797
  31 201 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 201 237 3 10 67 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 201 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 201 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 201 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 201 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 201 237 3 9 67 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 201 237 (Polychromatic418967fa.accept_10_6_1_7_1_342
  26 201 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 201 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 201 237 3 8 67 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 201 237 (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 201 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 201 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 201 237 3 7 67 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 201 237
  (Polychromatic418967fa.accept_8_4_1_5_1_186 20 201 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 201 237 (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 201 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 201 237 3 6 67 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 201 237 (Polychromatic418967fa.accept_15_2_6_12_1_1613
  17 201 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 237
  (Polychromatic418967fa.accept_10_6_1_7_1_342 16 201 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 201 237 3 5 67 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 201 237 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 201 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 237 (Polychromatic418967fa.accept_23_13_17_7_1_7726 13 201
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 201 237 3 4 67 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 201 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 201 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 201 237 (Polychromatic418967fa.accept_13_10_6_3_1_1515 10 201 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 201 237 3 3 67 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 201 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 201 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 237
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 201 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 201 237 3 2 67 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 201 237 (Polychromatic418967fa.accept_13_5_6_3_1_868 5 201 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 201 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 201 237 3 1 67 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 201 237
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 2 201 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 201 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 201 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 201 237))))))))))))))))))))))))))))))))))))) (allB_succ' 38 200 237 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 200 237 (accept_3_4 37 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 200 237 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 200 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 200 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 200 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 200 237 (accept_3_4 34 200 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 200 237 (Polychromatic418967fa.accept_7_5_4_6_1_167
  33 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 200 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 200 237 (accept_3_4 31 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 200 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 200 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 200 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 200 237 (accept_3_4 28 200 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 200 237 (Polychromatic418967fa.accept_13_1_5_3_1_888 27 200 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 200 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 200 237 (accept_3_4 25 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 200 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 200 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 200 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 200 237 (accept_3_4 22 200 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 200 237 (Polychromatic418967fa.accept_13_8_5_3_1_427 21 200 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 200 237
  (Polychromatic418967fa.accept_16_4_8_13_1_1059 20 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 200 237 (accept_3_4 19 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 200 237 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 200 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 200 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 200 237 (accept_3_4 16 200 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 200 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 200 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 200 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 200 237 (accept_3_4 13 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 200 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 200 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 200 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 200 237 (accept_3_4 10 200 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 200 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 200 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 200 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 200 237 (accept_3_4 7 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  200 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 200 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 200 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 200 237 (accept_3_4 4 200 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 200 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 200 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 200 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 200 237 (accept_3_4 1 200 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  237)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 199 237 (Eq.refl Bool.true) (allA_succ_of_accept 38 199 237
  (accept_3_5 38 199 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 199 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 199 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 199 237 (Polychromatic418967fa.accept_16_4_7_13_1_2795 36 199 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 199 237 (accept_3_5 35 199 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 199 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 199 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 199 237 (Polychromatic418967fa.accept_9_6_1_3_1_191
  33 199 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 199 237 (accept_3_5 32
  199 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 199 237
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 199 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 199 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 199 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 199 237 (accept_3_5 29 199 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 199 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 199 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 199 237 (Polychromatic418967fa.accept_11_5_1_6_1_774
  27 199 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 237 (accept_3_5 26
  199 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 199 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 199 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 199 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 199 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 199 237 (accept_3_5 23 199 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 199 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 199 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 199 237
  (Polychromatic418967fa.accept_22_21_1_17_1_14178 21 199 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 199 237 (accept_3_5 20 199 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 199 237 (Polychromatic418967fa.accept_25_19_24_12_1_14189 19 199 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  199 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 199 237 (accept_3_5 17
  199 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 199 237
  (Polychromatic418967fa.accept_6_4_1_3_1_77 16 199 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 199 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 199 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 237 (accept_3_5 14 199 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 199 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 199 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 237 (Polychromatic418967fa.accept_10_2_9_7_1_720
  12 199 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 199 237 (accept_3_5 11
  199 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 199 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 199 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 199 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 199 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 237 (accept_3_5 8 199 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 199 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 199 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  199 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 199 237 (accept_3_5 5 199
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 199 237 (Polychromatic418967fa.accept_6_4_1_3_1_77
  4 199 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 199 237
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 199 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 199 237 (accept_3_5 2 199 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  199 237 (Polychromatic418967fa.accept_13_1_4_3_1_1545 1 199 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 199 237))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 198 237 (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 198 237 3 13 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 198 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 198 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 198 237 (Polychromatic418967fa.accept_15_7_3_12_1_365
  37 198 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 198 237 3 12 66 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 198 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 198 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 198 237 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 198 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 198 237 3 11 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 198 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 32
  198 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 198 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 198 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 198 237 3 10 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 198 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 198 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 198 237 (Polychromatic418967fa.accept_12_4_6_9_1_548
  28 198 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 198 237 3 9 66 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 198 237
  (Polychromatic418967fa.accept_12_2_6_9_1_19 26 198 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 198 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 198 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 198 237 3 8 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 198 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23
  198 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 198 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 22 198 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 198 237 3 7 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 198 237 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 198 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 198 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 198 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 198 237 3 6 66 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 198 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 198 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 198 237 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 198 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 198 237 3 5 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 198 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 14
  198 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 198 237
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 198 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 198 237 3 4 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 198 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 198 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 198 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 198 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 198 237 3 3 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 198 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 198 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 198 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198 237 3 2 66 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 198 237
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 198 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 198 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 198 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 198 237 3 1 66 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 198 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 198 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 198 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 198 237)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 197 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 197 237 (accept_3_4 40 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 197 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 197 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 197 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 197 237 (accept_3_4 37 197 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 197 237 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 197 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 197 237
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 35 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 197 237 (accept_3_4 34 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 197 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 197 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 197 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 197 237 (accept_3_4 31 197 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 197 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 197 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 197 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 197 237 (accept_3_4 28 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 197 237 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 197 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 197 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 197 237 (accept_3_4 25 197 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 197 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 197 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 197 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 197 237 (accept_3_4 22 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 197 237 (Polychromatic418967fa.accept_14_7_1_13_1_357 21 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 197 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 197 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 197 237 (accept_3_4 19 197 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 197 237 (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 197 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 197 237
  (Polychromatic418967fa.accept_16_1_5_13_1_1025 17 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 197 237 (accept_3_4 16 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 197 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 197 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 197 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 237 (accept_3_4 13 197 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 197 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 197 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 197 237 (accept_3_4 10 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  197 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 197 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 197 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 237 (accept_3_4 7 197 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 197 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 197 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 197 237 (accept_3_4 4 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  197 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 197 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 197 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 197 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 237 (accept_3_4 1 197 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 197 237))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 196 237 (Eq.refl
  Bool.true) (allA_succ_of_accept 41 196 237 (accept_3_5 41 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 196 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 196 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 196 237 (Polychromatic418967fa.accept_16_7_4_13_1_1057 39 196
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 196 237 (accept_3_5 38 196
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 196 237
  (Polychromatic418967fa.accept_6_1_4_3_1_14 37 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 196 237 (Polychromatic418967fa.accept_11_3_9_6_1_105 36 196 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 196 237 (accept_3_5 35 196 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 196 237 (Polychromatic418967fa.accept_15_4_1_12_1_914 34 196 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 196 237
  (Polychromatic418967fa.accept_8_1_4_5_1_48 33 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 196 237 (accept_3_5 32 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 196 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 196 237 (Polychromatic418967fa.accept_12_6_4_9_1_544 30 196 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 196 237 (accept_3_5 29 196 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 196 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 196 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 196 237
  (Polychromatic418967fa.accept_17_10_9_16_1_5607 27 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 196 237 (accept_3_5 26 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 196 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 196 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 196 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 196 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 196 237 (accept_3_5 23 196 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 196 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 22
  196 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 196 237
  (Polychromatic418967fa.accept_10_1_6_7_1_710 21 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 196 237 (accept_3_5 20 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 196 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 196 237 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 196 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 196 237 (accept_3_5 17 196 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 196 237 (Polychromatic418967fa.accept_19_16_6_9_1_7335 16 196
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 196 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 196 237 (accept_3_5 14 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 196 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 196 237 (Polychromatic418967fa.accept_16_12_4_13_1_3827 12 196 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 196 237 (accept_3_5 11 196 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 196 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 196 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 196 237
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 196 237 (accept_3_5 8 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  196 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 196 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 196 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 196 237 (accept_3_5 5 196 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 196 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 196 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 196 237
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 196 237 (accept_3_5 2 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  196 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 196 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 196 237)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 195 237 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 195 237 3 14 65 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 195 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 195 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 195 237 (Polychromatic418967fa.accept_9_4_6_3_1_179
  40 195 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 195 237 3 13 65 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 195 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 195 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 195 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 195 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 195 237 3 12 65 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 195 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  195 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 195 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 195 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 195 237 3 11 65 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 195 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 195 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 237 (Polychromatic418967fa.accept_9_4_6_3_1_179
  31 195 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 195 237 3 10 65 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 195 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 195 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 195 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 195 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 195 237 3 9 65 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 195 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26
  195 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 195 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 195 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 195 237 3 8 65 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 195 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 195 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 195 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 195 237 3 7 65 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 195 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 195 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 195 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 195 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 195 237 3 6 65 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 195 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 17
  195 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 195 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 195 237 3 5 65 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 195 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 195 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 195 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 195 237 3 4 65 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 195 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 195 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 195 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 195 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 195 237 3 3 65 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 195 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 195 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 195 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 195 237 3 2 65 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 195 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 195 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 195 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 195 237 3 1 65 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 195 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 195 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 195 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 195 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 195 237))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 194 237
  (Eq.refl Bool.true) (allA_succ_of_accept 43 194 237 (accept_3_4 43 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 194 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 194 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 194 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 194 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 194 237 (accept_3_4 40 194 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 194 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  194 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 194 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 194 237 (accept_3_4 37 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 194 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 194 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 194 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 194 237 (accept_3_4 34 194 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 194 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 194 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 194 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 194 237 (accept_3_4 31 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 194 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 194 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 194 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 194 237 (accept_3_4 28 194 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 194 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 194 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 194 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 194 237 (accept_3_4 25 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 194 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 194 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 194 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 194 237 (accept_3_4 22 194 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 194 237 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 194 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 194 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 194 237 (accept_3_4 19 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 194 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 194 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 194 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 194 237 (accept_3_4 16 194 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 194 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 194 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 194 237
  (Polychromatic418967fa.accept_19_14_4_9_1_6009 14 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 194 237 (accept_3_4 13 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 194 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 194 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 194 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 194 237 (accept_3_4 10 194 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 194 237 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 194 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 194 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 194 237 (accept_3_4 7 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  194 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 194 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 194 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 194 237 (accept_3_4 4 194 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 194 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 194 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 194 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 194 237 (accept_3_4 1 194 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  237)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 193 237 (Eq.refl Bool.true) (allA_succ_of_accept 44 193
  237 (accept_3_5 44 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 193 237
  (Polychromatic418967fa.accept_9_7_4_3_1_204 43 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 193 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 193 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 193 237 (accept_3_5 41 193 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 193 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 193 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 193 237 (Polychromatic418967fa.accept_12_3_1_9_1_202
  39 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 193 237 (accept_3_5 38
  193 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 193 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 193 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 193 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 193 237 (accept_3_5 35 193 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 193 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 193 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 193 237 (Polychromatic418967fa.accept_7_5_4_6_1_167
  33 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 193 237 (accept_3_5 32
  193 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 193 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 193 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 193 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 193 237 (accept_3_5 29 193 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 193 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 193 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 193 237 (Polychromatic418967fa.accept_12_3_1_9_1_202
  27 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 193 237 (accept_3_5 26
  193 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 193 237
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 193 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 193 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 193 237 (accept_3_5 23 193 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 193 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 193 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 193 237
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 21 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 193 237 (accept_3_5 20 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 193 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 193 237 (Polychromatic418967fa.accept_13_5_11_3_1_902 18 193 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 193 237 (accept_3_5 17 193 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 193 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 193 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 193 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 193 237 (accept_3_5 14 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 193 237 (Polychromatic418967fa.accept_19_13_3_9_1_5980 13 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 193 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 193 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 193 237 (accept_3_5 11 193 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 193 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 193 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 193 237 (accept_3_5 8 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  193 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 193 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 193 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 193 237 (accept_3_5 5 193 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 193 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 193 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 193 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 193 237 (accept_3_5 2 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  193 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 193 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 193 237))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 192 237 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 192 237 3 15 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 192 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 192 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 192 237
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 43 192 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 192 237 3 14 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 192 237 (Polychromatic418967fa.accept_13_2_10_3_1_1538 41 192 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 192 237
  (Polychromatic418967fa.accept_21_19_3_6_1_2281 40 192 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 192 237 3 13 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 192 237 (Polychromatic418967fa.accept_17_4_5_16_1_3240 38 192 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 192 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 192 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 192 237 3 12 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 192 237 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 192 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 192 237 (Polychromatic418967fa.accept_10_4_2_7_1_373
  34 192 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 192 237 3 11 64 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 192 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 192 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 192 237 (Polychromatic418967fa.accept_14_3_10_13_1_339 31 192 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 192 237 3 10 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 192 237 (Polychromatic418967fa.accept_10_9_2_7_1_1096
  29 192 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 192 237
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 28 192 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 192 237 3 9 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 192 237 (Polychromatic418967fa.accept_18_8_12_3_1_2708 26 192 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 192 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 192 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 192 237 3 8 64 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 192 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 192 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 192 237 (Polychromatic418967fa.accept_20_2_12_17_1_5547 22 192 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 192 237 3 7 64 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 192 237
  (Polychromatic418967fa.accept_13_7_10_3_1_1505 20 192 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 192 237 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 192 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 192 237 3 6 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 192 237 (Polychromatic418967fa.accept_14_3_10_13_1_339
  17 192 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 192 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 16 192 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 192 237 3 5 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 192 237 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 192 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 192 237 (Polychromatic418967fa.accept_18_13_12_3_1_3857 13 192
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 237 3 4 64 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 192 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 192 237 (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 192 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 192 237 3 3 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 192 237 (Polychromatic418967fa.accept_18_8_12_3_1_2708 8 192 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 192 237
  (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 192 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 192 237 3 2 64 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 192 237 (Polychromatic418967fa.accept_10_5_2_7_1_345 5 192 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 192 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 192 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 192 237 3 1 64 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 192 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 192 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 192 237 (Polychromatic418967fa.accept_11_1_5_6_1_397 1 192 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 192 237)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 191 237
  (Eq.refl Bool.true) (allA_succ_of_accept 46 191 237 (accept_3_4 46 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 191 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 191 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 191 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 191 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 191 237 (accept_3_4 43 191 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 191 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 42
  191 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 191 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 191 237 (accept_3_4 40 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 191 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 191 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 191 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 191 237 (accept_3_4 37 191 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 191 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 191 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 191 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 191 237 (accept_3_4 34 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 191 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 191 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 191 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 191 237 (accept_3_4 31 191 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 191 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 191 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 191 237 (accept_3_4 28 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 191 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 191 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 191 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 237 (accept_3_4 25 191 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 191 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 191 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 191 237 (accept_3_4 22 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 191 237 (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 191 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 191 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 237 (accept_3_4 19 191 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 191 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 191 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 191 237 (accept_3_4 16 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 191 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 191 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 191 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 237 (accept_3_4 13 191 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 237 (Polychromatic418967fa.accept_13_12_9_3_1_3047 12 191 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 191 237 (accept_3_4 10 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  191 237 (Polychromatic418967fa.accept_21_9_2_6_1_12807 9 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 191 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 191 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 237 (accept_3_4 7 191 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 191 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 237 (accept_3_4 4 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 191 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 191 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 237 (accept_3_4 1 191 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 191 237))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 190 237 (Eq.refl
  Bool.true) (allA_succ_of_accept 47 190 237 (accept_3_5 47 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 190 237 (Polychromatic418967fa.accept_13_7_8_3_1_1533 46 190 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 190 237 (Polychromatic418967fa.accept_20_5_10_17_1_11478 45
  190 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 190 237 (accept_3_5 44
  190 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 190 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 190 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 190 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 190 237 (accept_3_5 41 190 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 190 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 190 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 190 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  190 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 190 237 (accept_3_5 38
  190 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 190 237
  (Polychromatic418967fa.accept_6_1_4_3_1_14 37 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 190 237 (Polychromatic418967fa.accept_15_6_10_12_1_2538 36 190 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 190 237 (accept_3_5 35 190 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 190 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 190 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 190 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 190 237 (accept_3_5 32 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 190 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 190 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 190 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 190 237 (accept_3_5 29 190 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 190 237 (Polychromatic418967fa.accept_15_13_10_12_1_2503 28 190 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 190 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 190 237 (accept_3_5 26 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 190 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 190 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 190 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 190 237 (accept_3_5 23 190 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 190 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 190 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 190 237
  (Polychromatic418967fa.accept_14_7_8_13_1_3161 21 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 190 237 (accept_3_5 20 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 190 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 190 237 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 190 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 190 237 (accept_3_5 17 190 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 190 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 190 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 190 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 190 237 (accept_3_5 14 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 190 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 190 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 190 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 190 237 (accept_3_5 11 190 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 190 237 (Polychromatic418967fa.accept_16_10_14_13_1_1870 10 190 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 190 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 190 237 (accept_3_5 8 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  190 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 190 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 190 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 190 237 (accept_3_5 5 190 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 190 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 190 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 190 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 190 237 (accept_3_5 2 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  190 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 190 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 190 237)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 189 237 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 189 237 3 16 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 189 237 (Polychromatic418967fa.accept_13_8_7_3_1_430 47 189 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 189 237
  (Polychromatic418967fa.accept_19_8_18_9_1_10160 46 189 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 189 237 3 15 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 189 237 (Polychromatic418967fa.accept_15_14_9_12_1_2498 44 189 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 189 237
  (Polychromatic418967fa.accept_13_4_7_3_1_92 43 189 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 189 237 3 14 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 189 237 (Polychromatic418967fa.accept_19_3_18_9_1_4580 41 189 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 237
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 40 189 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 189 237 3 13 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 189 237 (Polychromatic418967fa.accept_10_8_9_7_1_1118 38 189 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 237
  (Polychromatic418967fa.accept_11_4_2_6_1_389 37 189 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 189 237 3 12 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 189 237 (Polychromatic418967fa.accept_13_9_7_3_1_1531 35 189 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 237
  (Polychromatic418967fa.accept_13_8_7_3_1_430 34 189 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 189 237 3 11 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 189 237 (Polychromatic418967fa.accept_10_2_9_7_1_720 32 189 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 237
  (Polychromatic418967fa.accept_17_14_2_16_1_4380 31 189 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 189 237 3 10 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 189 237 (Polychromatic418967fa.accept_14_1_7_13_1_333 29 189 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 237
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 28 189 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 189 237 3 9 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 189 237 (Polychromatic418967fa.accept_11_4_2_6_1_389 26 189 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 237 (Polychromatic418967fa.accept_15_10_9_12_1_2497 25 189
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 189 237 3 8 63 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 189 237
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 23 189 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 189 237 (Polychromatic418967fa.accept_10_2_9_7_1_720 22 189 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 189 237 3 7 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 189 237 (Polychromatic418967fa.accept_14_6_7_13_1_3158
  20 189 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 237
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 189 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 189 237 3 6 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 189 237 (Polychromatic418967fa.accept_13_4_7_3_1_92 17 189 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 237 (Polychromatic418967fa.accept_19_16_18_9_1_3295 16 189
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 189 237 3 5 63 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 189 237
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 14 189 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 189 237 (Polychromatic418967fa.accept_18_13_9_3_1_5114 13 189 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 189 237 3 4 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 189 237 (Polychromatic418967fa.accept_13_11_7_3_1_894
  11 189 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 237
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 10 189 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 189 237 3 3 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 189 237 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 189 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 237 (Polychromatic418967fa.accept_18_7_9_3_1_800 7 189 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 189 237 3 2 63 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 189 237
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 189 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 237 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 189 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 189 237 3 1 63 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 189 237 (Polychromatic418967fa.accept_10_2_9_7_1_720 2 189 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 237
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 1 189 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 189 237))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 188 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 188 237 (accept_3_4 49 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 188 237 (Polychromatic418967fa.accept_13_9_6_3_1_1514 48 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 188 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 188 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 188 237 (accept_3_4 46 188 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 188 237 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 188 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 188 237
  (Polychromatic418967fa.accept_13_5_6_3_1_868 44 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 188 237 (accept_3_4 43 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 188 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 188 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 188 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 188 237 (accept_3_4 40 188 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 188 237 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 188 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 188 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 38 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 188 237 (accept_3_4 37 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 188 237 (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 188 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 188 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 188 237 (accept_3_4 34 188 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 188 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 188 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 188 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 32 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 188 237 (accept_3_4 31 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 188 237 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 188 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 188 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 188 237 (accept_3_4 28 188 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 188 237 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 188 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 188 237
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 26 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 188 237 (accept_3_4 25 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 188 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 188 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 188 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 188 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 188 237 (accept_3_4 22 188 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 188 237
  (Polychromatic418967fa.accept_14_7_6_13_1_4111 21 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 188 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 188 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 188 237 (accept_3_4 19 188 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 188 237 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 188 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 188 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 188 237 (accept_3_4 16 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 188 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 188 237 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 188 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 188 237 (accept_3_4 13 188 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 188 237 (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 188 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 188 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 188 237 (accept_3_4 10 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  188 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 188 237 (Polychromatic418967fa.accept_16_8_12_13_1_3851 8 188 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 188 237 (accept_3_4 7 188 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 188 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 188 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 188 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 188 237 (accept_3_4 4 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  188 237 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 188 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 188 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 188 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 188 237 (accept_3_4 1 188 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 188 237)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 187 237
  (Eq.refl Bool.true) (allA_succ_of_accept 50 187 237 (accept_3_5 50 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 187 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 187 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 187 237 (Polychromatic418967fa.accept_13_9_5_3_1_428 48 187
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 187 237 (accept_3_5 47 187
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 187 237 (Polychromatic418967fa.accept_4_2_3_1_1_2
  46 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 187 237
  (Polychromatic418967fa.accept_13_6_5_3_1_426 45 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 187 237 (accept_3_5 44 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 187 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 187 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 187 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 187 237 (accept_3_5 41 187 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 187 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 187 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 187 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 187 237 (accept_3_5 38 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 187 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 187 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 187 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 187 237 (accept_3_5 35 187 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 187 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 187 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 187 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 187 237 (accept_3_5 32 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 187 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 187 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 187 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 187 237 (accept_3_5 29 187 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 187 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 187 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 187 237
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 187 237 (accept_3_5 26 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 187 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 187 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 187 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 187 237 (accept_3_5 23 187 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 187 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 187 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 187 237
  (Polychromatic418967fa.accept_13_8_5_3_1_427 21 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 187 237 (accept_3_5 20 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 187 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 187 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 187 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 187 237 (accept_3_5 17 187 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 187 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 187 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 187 237 (accept_3_5 14 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 187 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 187 237 (Polychromatic418967fa.accept_18_12_7_3_1_2666 12 187 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 237 (accept_3_5 11 187 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 187 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 187 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 237
  (Polychromatic418967fa.accept_13_9_5_3_1_428 9 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 187 237 (accept_3_5 8 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  187 237 (Polychromatic418967fa.accept_19_7_16_9_1_398 7 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 187 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 187 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 237 (accept_3_5 5 187 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 187 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 237
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 237 (accept_3_5 2 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 187 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187 237))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 186 237 (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 186 237 3 17 62 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 186 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 186 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 186 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 186 237 3 16 62 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 186 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 186 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 186 237 (Polychromatic418967fa.accept_9_1_6_3_1_177
  46 186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 186 237 3 15 62 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 186 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 186 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 186 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 186 237 3 14 62 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 186 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 41
  186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 186 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 40 186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 186 237 3 13 62 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 186 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 186 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 186 237 (Polychromatic418967fa.accept_7_2_4_6_1_166
  37 186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 186 237 3 12 62 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 186 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 186 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 34 186 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 186 237 3 11 62 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 186 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 186 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 237 3 10 62 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 186 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 186 237 (Polychromatic418967fa.accept_9_1_6_3_1_177
  28 186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 186 237 3 9 62 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 186 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 186 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 186 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 186 237 3 8 62 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 186 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23
  186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 186 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 186 237 3 7 62 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 186 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 186 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 186 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 186 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 186 237 3 6 62 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 186 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 186 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 186 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 186 237 3 5 62 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 186 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 14
  186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 186 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 237 3 4 62 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 186 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 186 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 186 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 186 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 186 237 3 3 62 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 186 237
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 186 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 186 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186 237 3 2 62 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 186 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 186 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 186 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 186 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 186 237 3 1 62 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 186 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 186 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 186 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  237)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 185 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 185 237 (accept_3_4 52 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 185 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 185 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 185 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 185 237 (accept_3_4 49 185 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 185 237 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 185 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 185 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 185 237 (accept_3_4 46 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 185 237 (Polychromatic418967fa.accept_17_11_15_16_1_4377 45 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 44 185 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 185 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 185 237 (accept_3_4 43 185 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 185 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 185 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 185 237
  (Polychromatic418967fa.accept_19_3_14_9_1_8866 41 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 185 237 (accept_3_4 40 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 185 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 185 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 185 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 185 237 (accept_3_4 37 185 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 185 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 185 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 185 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 185 237 (accept_3_4 34 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 185 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 185 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 185 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 185 237 (accept_3_4 31 185 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 185 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 185 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 185 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 185 237 (accept_3_4 28 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 185 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 185 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 185 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 185 237 (accept_3_4 25 185 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 185 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 185 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 185 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 185 237 (accept_3_4 22 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 185 237 (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 185 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 185 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 185 237 (accept_3_4 19 185 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 185 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 185 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 185 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 185 237 (accept_3_4 16 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 185 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 185 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 185 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 237 (accept_3_4 13 185 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 185 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 185 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 185 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 185 237 (accept_3_4 10 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  185 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 185 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 185 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 237 (accept_3_4 7 185 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 185 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 185 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 185 237
  (Polychromatic418967fa.accept_16_5_9_13_1_3845 5 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 185 237 (accept_3_4 4 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  185 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 185 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 185 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 185 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 237 (accept_3_4 1 185 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 185 237))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 184 237
  (Eq.refl Bool.true) (allA_succ_of_accept 53 184 237 (accept_3_5 53 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 184 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 184 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 184 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 184 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 184 237 (accept_3_5 50 184 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 184 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 49
  184 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 184 237
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 48 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 184 237 (accept_3_5 47 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 184 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 184 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 184 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 184 237 (accept_3_5 44 184 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 184 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 184 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 184 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 184 237 (accept_3_5 41 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 184 237 (Polychromatic418967fa.accept_13_1_2_3_1_911 40 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 184 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 184 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 184 237 (accept_3_5 38 184 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 184 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 184 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 184 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 184 237 (accept_3_5 35 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 184 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 184 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 184 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 184 237 (accept_3_5 32 184 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 184 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 184 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 184 237
  (Polychromatic418967fa.accept_12_6_4_9_1_544 30 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 184 237 (accept_3_5 29 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 184 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 184 237 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 184 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 184 237 (accept_3_5 26 184 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 184 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 184 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 184 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 184 237 (accept_3_5 23 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 184 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 184 237 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 184 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 184 237 (accept_3_5 20 184 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 184 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 184 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 184 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 184 237 (accept_3_5 17 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 184 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 184 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 184 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 184 237 (accept_3_5 14 184 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 184 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 184 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 184 237
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 184 237 (accept_3_5 11 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 184 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 184 237 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 184 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 184 237 (accept_3_5 8 184 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 184 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 184 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 184 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 184 237 (accept_3_5 5 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  184 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 184 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 184 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 184 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 184 237 (accept_3_5 2 184 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 184 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 184 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 183 237 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 183 237 3 18 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 183 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 53 183 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 183 237 (Polychromatic418967fa.accept_15_7_3_12_1_365 52 183
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 183 237 3 17 61 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 183 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 183 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 183 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 183 237 3 16 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 183 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 47
  183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 183 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 183 237 3 15 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 183 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 183 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 237 (Polychromatic418967fa.accept_12_7_3_9_1_999
  43 183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 183 237 3 14 61 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 183 237
  (Polychromatic418967fa.accept_12_5_3_9_1_541 41 183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 183 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 183 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 183 237 3 13 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 183 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 38
  183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 183 237 3 12 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 183 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 183 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 183 237 3 11 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 183 237 (Polychromatic418967fa.accept_13_6_1_3_1_1522 32 183 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 237
  (Polychromatic418967fa.accept_12_7_3_9_1_999 31 183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 183 237 3 10 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 183 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 183 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 237 (Polychromatic418967fa.accept_13_2_1_3_1_419
  28 183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 183 237 3 9 61 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 183 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 183 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 183 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 183 237 3 8 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 183 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 23
  183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 183 237 3 7 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 183 237 (Polychromatic418967fa.accept_13_7_1_3_1_1523 20 183 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 183 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 183 237 3 6 61 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 183 237
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 183 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 183 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 183 237 3 5 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 183 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14
  183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 237
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 183 237 3 4 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 183 237 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 183 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 183 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 183 237 3 3 61 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 183 237
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 183 237 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 183 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 183 237 3 2 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 183 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 183 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 237
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 183 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 183 237 3 1 61 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 183 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 183 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 237 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 183 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 182 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 182 237 (accept_3_4 55 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 182 237 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 182 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 182 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 182 237 (accept_3_4 52 182 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 182 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 182 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 182 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 50 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 182 237 (accept_3_4 49 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 182 237 (Polychromatic418967fa.accept_15_3_2_12_1_2469 48 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 182 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 182 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 182 237 (accept_3_4 46 182 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 182 237 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 182 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 182 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 44 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 182 237 (accept_3_4 43 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 182 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 182 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 182 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 182 237 (accept_3_4 40 182 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 182 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 182 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 182 237
  (Polychromatic418967fa.accept_20_18_2_17_1_14188 38 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 182 237 (accept_3_4 37 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 182 237 (Polychromatic418967fa.accept_15_6_2_12_1_885 36 182 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 182 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 182 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 182 237 (accept_3_4 34 182 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 182 237 (Polychromatic418967fa.accept_9_6_2_3_1_771
  33 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 182 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 182 237 (accept_3_4 31 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 182 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 182 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 182 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 182 237 (accept_3_4 28 182 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 182 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 182 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 182 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 182 237 (accept_3_4 25 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 182 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 182 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 182 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 182 237 (accept_3_4 22 182 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 182 237 (Polychromatic418967fa.accept_15_6_2_12_1_885 21 182 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 182 237
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 20 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 182 237 (accept_3_4 19 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 182 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 182 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 182 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 182 237 (accept_3_4 16 182 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 182 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 182 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 182 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 182 237 (accept_3_4 13 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 182 237 (Polychromatic418967fa.accept_18_12_2_3_1_6414 12 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 182 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 182 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 182 237 (accept_3_4 10 182 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 182 237 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 182 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 182 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 182 237 (accept_3_4 7 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  182 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 182 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 182 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 182 237 (accept_3_4 4 182 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 182 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 182 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 182 237
  (Polychromatic418967fa.accept_19_2_11_9_1_1119 2 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 182 237 (accept_3_4 1 182 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 181 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 56 181 237 (accept_3_5 56 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 181 237 (Polychromatic418967fa.accept_22_11_5_17_1_4659 55 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 181 237 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 181 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 181 237 (accept_3_5 53 181 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 181 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 181 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 181 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 51 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 181 237 (accept_3_5 50 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 181 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 181 237 (Polychromatic418967fa.accept_13_9_12_3_1_907 48 181 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 181 237 (accept_3_5 47 181 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 181 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 181 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 181 237
  (Polychromatic418967fa.accept_11_1_5_6_1_397 45 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 181 237 (accept_3_5 44 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 181 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 181 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 181 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 181 237 (accept_3_5 41 181 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 181 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 181 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 181 237
  (Polychromatic418967fa.accept_12_3_1_9_1_202 39 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 181 237 (accept_3_5 38 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 181 237 (Polychromatic418967fa.accept_19_18_10_9_1_5996 37 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 181 237 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 181 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 181 237 (accept_3_5 35 181 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 181 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 181 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 33 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 181 237 (accept_3_5 32 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 181 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 181 237 (Polychromatic418967fa.accept_13_4_12_3_1_2999 30 181 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 237 (accept_3_5 29 181 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 181 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 181 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 237
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 181 237 (accept_3_5 26 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 181 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 237 (accept_3_5 23 181 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 181 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 237
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 237 (accept_3_5 20 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 237 (Polychromatic418967fa.accept_15_4_1_12_1_914 19 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 237 (Polychromatic418967fa.accept_16_2_5_13_1_3842 18 181 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 237 (accept_3_5 17 181 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 181 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 237 (accept_3_5 14 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 237 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 181 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 237 (accept_3_5 11 181 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 181 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 237
  (Polychromatic418967fa.accept_13_9_12_3_1_907 9 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 237 (accept_3_5 8 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 181 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 237 (accept_3_5 5 181 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 181 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 237
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 237 (accept_3_5 2 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 237 (Polychromatic418967fa.accept_11_1_5_6_1_397 1 181 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 237))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 180 237 (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 180 237 3 19 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 56 180 237 (Polychromatic418967fa.accept_16_8_4_13_1_1014 56 180 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 180 237
  (Polychromatic418967fa.accept_16_7_4_13_1_1057 55 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 180 237 3 18 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 180 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 180 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 180 237
  (Polychromatic418967fa.accept_21_10_12_6_1_5124 52 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 180 237 3 17 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 180 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 180 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 180 237
  (Polychromatic418967fa.accept_8_1_4_5_1_48 49 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 180 237 3 16 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 180 237 (Polychromatic418967fa.accept_13_8_11_3_1_3053 47 180 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 180 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 46 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 180 237 3 15 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 180 237 (Polychromatic418967fa.accept_13_5_11_3_1_902 44 180 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 180 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 180 237 3 14 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 180 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 180 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 180 237 (Polychromatic418967fa.accept_13_1_11_3_1_901
  40 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 180 237 3 13 60 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 180 237
  (Polychromatic418967fa.accept_16_6_4_13_1_3841 38 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 180 237 (Polychromatic418967fa.accept_21_16_12_6_1_8274 37 180 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 180 237 3 12 60 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 180 237
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 35 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 180 237 (Polychromatic418967fa.accept_13_8_11_3_1_3053 34 180 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 180 237 3 11 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 180 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 32
  180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 180 237
  (Polychromatic418967fa.accept_13_5_11_3_1_902 31 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 237 3 10 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 180 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 180 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 180 237 (Polychromatic418967fa.accept_13_2_11_3_1_873
  28 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 180 237 3 9 60 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 180 237
  (Polychromatic418967fa.accept_17_9_10_16_1_3217 26 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 180 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 180 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 180 237 3 8 60 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 180 237
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 23 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 180 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 180 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 180 237 3 7 60 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 180 237
  (Polychromatic418967fa.accept_13_7_11_3_1_1540 20 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 180 237 (Polychromatic418967fa.accept_21_19_12_6_1_6689 19 180 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 180 237 3 6 60 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 180 237
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 180 237 (Polychromatic418967fa.accept_21_16_12_6_1_8274 16 180 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 180 237 3 5 60 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 180 237
  (Polychromatic418967fa.accept_13_1_11_3_1_901 14 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 180 237 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 180 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 237 3 4 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 11
  180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 180 237
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 10 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 180 237 3 3 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 180 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 180 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 180 237 (Polychromatic418967fa.accept_13_7_11_3_1_1540
  7 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 237 3 2 60 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 180 237
  (Polychromatic418967fa.accept_13_5_11_3_1_902 5 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 180 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 180 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 180 237 3 1 60 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 180 237 (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 180 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 180 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 180 237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 179 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 179 237 (accept_3_4 58 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 179 237 (Polychromatic418967fa.accept_17_6_9_16_1_4410 57 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 179 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 179 237 (accept_3_4 55 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 179 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 179 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 179 237
  (Polychromatic418967fa.accept_11_9_3_6_1_797 53 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 179 237 (accept_3_4 52 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 179 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 179 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 179 237 (accept_3_4 49 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 179 237 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 179 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 179 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 179 237 (accept_3_4 46 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 179 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 179 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 179 237 (accept_3_4 43 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 179 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 179 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 179 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 41 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 179 237 (accept_3_4 40 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 179 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 179 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 179 237 (accept_3_4 37 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 179 237 (Polychromatic418967fa.accept_19_17_8_9_1_10148 36 179 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 179 237
  (Polychromatic418967fa.accept_19_16_8_9_1_8858 35 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 179 237 (accept_3_4 34 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 179 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 179 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 179 237 (accept_3_4 31 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 179 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 179 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 179 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 179 237 (accept_3_4 28 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 179 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 179 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 179 237 (accept_3_4 25 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 179 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 179 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 179 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 179 237 (accept_3_4 22 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 179 237 (Polychromatic418967fa.accept_32_21_19_13_1_14187 21 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 179 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 237 (accept_3_4 19 179 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 179 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 179 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 179 237 (accept_3_4 16 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 179 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 179 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 237 (accept_3_4 13 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 179 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 179 237 (accept_3_4 10 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  179 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 179 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 237 (accept_3_4 7 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 179 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 237 (accept_3_4 4 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 179 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 237 (accept_3_4 1 179 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 179 237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 178
  237 (Eq.refl Bool.true) (allA_succ_of_accept 59 178 237 (accept_3_5 59 178 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 178 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 178 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 178 237 (Polychromatic418967fa.accept_13_5_9_3_1_870
  57 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 178 237 (accept_3_5 56
  178 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 178 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 55 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 178 237 (Polychromatic418967fa.accept_12_6_10_9_1_531 54 178 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 178 237 (accept_3_5 53 178 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 178 237 (Polychromatic418967fa.accept_23_6_17_7_1_9295 52 178 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 178 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 178 237 (accept_3_5 50 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 178 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 178 237 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 178 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 178 237 (accept_3_5 47 178 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 178 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 178 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 178 237
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 178 237 (accept_3_5 44 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 178 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 178 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 178 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 178 237 (accept_3_5 41 178 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 178 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 178 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 178 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 178 237 (accept_3_5 38 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 178 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 178 237 (Polychromatic418967fa.accept_17_2_8_16_1_4403 36 178 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 178 237 (accept_3_5 35 178 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 178 237 (Polychromatic418967fa.accept_13_8_9_3_1_2213 34 178
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 178 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 178 237 (accept_3_5 32 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 178 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 178 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 178 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 178 237 (accept_3_5 29 178 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 178 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 178 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 178 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 178 237 (accept_3_5 26 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 178 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 178 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 178 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 178 237 (accept_3_5 23 178 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 178 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 178 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 178 237
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 178 237 (accept_3_5 20 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 178 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 178 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 178 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 178 237 (accept_3_5 17 178 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 178 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 178 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 178 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 178 237 (accept_3_5 14 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 178 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 178 237 (Polychromatic418967fa.accept_13_12_9_3_1_3047 12 178 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 178 237 (accept_3_5 11 178 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 178 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 178 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 178 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 178 237 (accept_3_5 8 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  178 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 178 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 178 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 178 237 (accept_3_5 5 178 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 178 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 178 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 178 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 178 237 (accept_3_5 2 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  178 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 178 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 178 237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 177 237
  (Eq.refl Bool.true) (allA_succ_of_gcd 60 177 237 3 20 59 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 177 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 177 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 177 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 58 177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 177 237 3 19 59 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 177 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 56 177 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 177 237 (Polychromatic418967fa.accept_9_1_6_3_1_177
  55 177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 177 237 3 18 59 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 177 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 177 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 177 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 177 237 3 17 59 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 177 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 50
  177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 177 237 3 16 59 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 177 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 177 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 237 (Polychromatic418967fa.accept_7_4_2_6_1_337
  46 177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 177 237 3 15 59 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 177 237
  (Polychromatic418967fa.accept_8_4_1_5_1_186 44 177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 177 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 177 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 177 237 3 14 59 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 177 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 41
  177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 40 177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 177 237 3 13 59 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 177 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 177 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 237 (Polychromatic418967fa.accept_9_1_6_3_1_177
  37 177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 177 237 3 12 59 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 177 237
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 177 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 34 177 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 177 237 3 11 59 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 177 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 32
  177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 177 237 3 10 59 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 177 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 177 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 237 (Polychromatic418967fa.accept_8_4_1_5_1_186
  28 177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 177 237 3 9 59 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 177 237
  (Polychromatic418967fa.accept_9_8_6_3_1_457 26 177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 177 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 177 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 177 237 3 8 59 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 177 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 23
  177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 22 177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 177 237 3 7 59 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 177 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 177 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 177 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 177 237 3 6 59 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 177 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 177 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 177 237 3 5 59 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 177 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 14
  177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 177 237 3 4 59 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 177 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 177 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 177 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 177 237 3 3 59 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 177 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 177 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 177 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 177 237 3 2 59 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 177 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 177 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 177 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 177 237 3 1 59 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 177 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 177 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 177 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 176 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 176 237 (accept_3_4 61 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 176 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 176 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 176 237 (accept_3_4 58 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 176 237 (Polychromatic418967fa.accept_21_15_8_6_1_5106 57 176 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 176 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 56 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 176 237 (accept_3_4 55 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 176 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 176 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 176 237 (accept_3_4 52 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 176 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 176 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 176 237
  (Polychromatic418967fa.accept_13_11_7_3_1_894 50 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 176 237 (accept_3_4 49 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 176 237 (Polychromatic418967fa.accept_13_9_7_3_1_1531 48 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 176 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 176 237 (accept_3_4 46 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 176 237 (Polychromatic418967fa.accept_18_9_14_3_1_6407 45 176 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 176 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 176 237 (accept_3_4 43 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 176 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 176 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 176 237 (accept_3_4 40 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 176 237 (Polychromatic418967fa.accept_19_1_5_9_1_10341 39 176 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 176 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 176 237 (accept_3_4 37 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 176 237 (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 176 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 176 237 (accept_3_4 34 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 176 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 176 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 176 237
  (Polychromatic418967fa.accept_19_13_5_9_1_3318 32 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 176 237 (accept_3_4 31 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 176 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 176 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 176 237 (accept_3_4 28 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 176 237 (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 176 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 176 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 176 237 (accept_3_4 25 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 176 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 176 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 176 237 (accept_3_4 22 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 176 237 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 176 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 176 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 176 237 (accept_3_4 19 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 176 237 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 176 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 176 237 (accept_3_4 16 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 176 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 176 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 176 237
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 14 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 176 237 (accept_3_4 13 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 176 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 176 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 176 237 (accept_3_4 10 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 176 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 176 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 176 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 176 237 (accept_3_4 7 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  176 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 176 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 176 237 (accept_3_4 4 176 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 176 237 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 176 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 176 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 176 237 (accept_3_4 1 176 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 175 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 62 175 237 (accept_3_5 62 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 175 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 61 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 175 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 60 175 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 175 237 (accept_3_5 59 175 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 175 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 175 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 175 237
  (Polychromatic418967fa.accept_13_5_6_3_1_868 57 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 175 237 (accept_3_5 56 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 175 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 55 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 175 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 175 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 175 237 (accept_3_5 53 175 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 175 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 175 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 175 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 51 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 175 237 (accept_3_5 50 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 175 237 (Polychromatic418967fa.accept_11_5_10_6_1_793 49 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 175 237 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 175 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 175 237 (accept_3_5 47 175 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 175 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 175 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 175 237
  (Polychromatic418967fa.accept_17_11_5_16_1_5600 45 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 175 237 (accept_3_5 44 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 175 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 175 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 175 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 175 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 175 237 (accept_3_5 41 175 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 175 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40
  175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 175 237
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 175 237 (accept_3_5 38 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 175 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 175 237 (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 175 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 175 237 (accept_3_5 35 175 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 175 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 175 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 175 237 (accept_3_5 32 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 175 237 (Polychromatic418967fa.accept_13_5_6_3_1_868 31 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 175 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 175 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 175 237 (accept_3_5 29 175 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 175 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 175 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 175 237
  (Polychromatic418967fa.accept_11_5_10_6_1_793 27 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 175 237 (accept_3_5 26 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 175 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 175 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 175 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 237 (accept_3_5 23 175 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 175 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 237
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 21 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 175 237 (accept_3_5 20 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 175 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 175 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 175 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 175 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 237 (accept_3_5 17 175 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 175 237 (accept_3_5 14 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 175 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 237 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 175 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 237 (accept_3_5 11 175 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 175 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 237
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 237 (accept_3_5 8 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  175 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 175 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 175 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 237 (accept_3_5 5 175 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 175 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 237
  (Polychromatic418967fa.accept_10_3_5_7_1_330 3 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 237 (accept_3_5 2 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 175 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175 237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 174 237
  (Eq.refl Bool.true) (allA_succ_of_gcd 63 174 237 3 21 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 174 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 62 174 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 174 237
  (Polychromatic418967fa.accept_10_1_4_7_1_374 61 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 174 237 3 20 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 174 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 174 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 174 237 (Polychromatic418967fa.accept_11_3_9_6_1_105
  58 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 174 237 3 19 58 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 174 237
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 56 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 174 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 174 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 174 237 3 18 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 174 237 (Polychromatic418967fa.accept_10_3_4_7_1_353
  53 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 174 237
  (Polychromatic418967fa.accept_10_2_4_7_1_352 52 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 174 237 3 17 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 174 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 50 174 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 174 237
  (Polychromatic418967fa.accept_14_7_6_13_1_4111 49 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 237 3 16 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 174 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 174 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 174 237 (Polychromatic418967fa.accept_12_10_6_9_1_549
  46 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 174 237 3 15 58 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 174 237
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 174 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 174 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 174 237 3 14 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 174 237 (Polychromatic418967fa.accept_10_1_4_7_1_374
  41 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 174 237
  (Polychromatic418967fa.accept_12_4_6_9_1_548 40 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 174 237 3 13 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 174 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 38 174 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 174 237 (Polychromatic418967fa.accept_13_11_5_3_1_889
  37 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 174 237 3 12 58 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 174 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 174 237 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 174 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 174 237 3 11 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 174 237 (Polychromatic418967fa.accept_10_2_4_7_1_352
  32 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 174 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 237 3 10 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 237 (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 174 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 174 237
  (Polychromatic418967fa.accept_12_4_6_9_1_548 28 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 174 237 3 9 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 174 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 174 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 174 237 (Polychromatic418967fa.accept_11_3_9_6_1_105 25 174
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 174 237 3 8 58 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 174 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 174 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 174 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 174 237 3 7 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 174 237 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  20 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 174 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 237 3 6 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 174 237 (Polychromatic418967fa.accept_16_1_14_13_1_3834 17 174 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 174 237 (Polychromatic418967fa.accept_12_4_6_9_1_548
  16 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 174 237 3 5 58 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 174 237
  (Polychromatic418967fa.accept_11_3_9_6_1_105 14 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 174 237 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 174 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 174 237 3 4 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 174 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 174 237
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 174 237 3 3 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 174 237 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 174 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 174 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 174 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 237 3 2 58 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 237
  (Polychromatic418967fa.accept_14_5_6_13_1_3145 5 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 174 237 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 174 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 174 237 3 1 58 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 174 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 174 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 237
  (Polychromatic418967fa.accept_10_1_4_7_1_374 1 174 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 174 237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 173 237 (Eq.refl
  Bool.true) (allA_succ_of_accept 64 173 237 (accept_3_4 64 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 173 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 173 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 173 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 173 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 173 237 (accept_3_4 61 173 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 173 237 (Polychromatic418967fa.accept_7_4_5_6_1_344
  60 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 173 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 59 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 173 237 (accept_3_4 58 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 173 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 173 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 173 237 (accept_3_4 55 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 173 237 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 173 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 173 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 173 237 (accept_3_4 52 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 173 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 173 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 173 237 (accept_3_4 49 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 173 237 (Polychromatic418967fa.accept_14_6_5_13_1_367 48 173 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 173 237
  (Polychromatic418967fa.accept_11_3_8_6_1_788 47 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 173 237 (accept_3_4 46 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 173 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 173 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 173 237 (accept_3_4 43 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 173 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 173 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 173 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 173 237 (accept_3_4 40 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 173 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 173 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 173 237 (accept_3_4 37 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 173 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 173 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 173 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 173 237 (accept_3_4 34 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 173 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 173 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 173 237 (accept_3_4 31 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 173 237 (Polychromatic418967fa.accept_17_13_3_16_1_5599 30 173 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 173 237 (accept_3_4 28 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 173 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 173 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 173 237 (accept_3_4 25 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 173 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 173 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 173 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 173 237 (accept_3_4 22 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 173 237 (Polychromatic418967fa.accept_17_4_3_16_1_9483 21 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 173 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 237 (accept_3_4 19 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 173 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 173 237 (accept_3_4 16 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 173 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 173 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 237 (accept_3_4 13 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 237 (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 173 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 173 237 (accept_3_4 10 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  173 237 (Polychromatic418967fa.accept_26_9_17_3_1_14186 9 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 173 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 237 (accept_3_4 7 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 173 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 173 237 (accept_3_4 4 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  173 237 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 173 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 173 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 237 (accept_3_4 1 173 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 173 237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66
  172 237 (Eq.refl Bool.true) (allA_succ_of_accept 65 172 237 (accept_3_5 65 172 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 172 237 (Polychromatic418967fa.accept_10_4_2_7_1_373 64 172 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 172 237
  (Polychromatic418967fa.accept_15_3_7_12_1_372 63 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 172 237 (accept_3_5 62 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 172 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 172 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 60 172 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 172 237 (accept_3_5 59 172 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 172 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 172 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 172 237
  (Polychromatic418967fa.accept_8_1_4_5_1_48 57 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 172 237 (accept_3_5 56 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 172 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 172 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 172 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 172 237 (accept_3_5 53 172 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 172 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 172 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 172 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 172 237 (accept_3_5 50 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 172 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 172 237 (Polychromatic418967fa.accept_15_3_7_12_1_372 48 172 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 172 237 (accept_3_5 47 172 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 172 237 (Polychromatic418967fa.accept_19_8_1_9_1_7329 46 172
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 172 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 172 237 (accept_3_5 44 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 172 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 172 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 172 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 172 237 (accept_3_5 41 172 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 172 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 172 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 172 237
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 172 237 (accept_3_5 38 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 172 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 172 237 (Polychromatic418967fa.accept_15_6_7_12_1_869 36 172 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 172 237 (accept_3_5 35 172 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 172 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 172 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 172 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 172 237 (accept_3_5 32 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 172 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 172 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 172 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 172 237 (accept_3_5 29 172 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 172 237 (Polychromatic418967fa.accept_21_7_4_6_1_11287 28 172 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 172 237
  (Polychromatic418967fa.accept_19_8_1_9_1_7329 27 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 172 237 (accept_3_5 26 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 172 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 172 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 172 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 172 237 (accept_3_5 23 172 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 172 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 172 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 172 237
  (Polychromatic418967fa.accept_15_6_7_12_1_869 21 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 172 237 (accept_3_5 20 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 172 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 172 237 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 172 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 172 237 (accept_3_5 17 172 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 172 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 172 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 172 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 172 237 (accept_3_5 14 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 172 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 172 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 172 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 172 237 (accept_3_5 11 172 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 172 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 172 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 172 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 172 237 (accept_3_5 8 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  172 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 172 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 172 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 172 237 (accept_3_5 5 172 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 172 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 172 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 172 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 172 237 (accept_3_5 2 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  172 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 172 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 172 237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 171 237
  (Eq.refl Bool.true) (allA_succ_of_gcd 66 171 237 3 22 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 171 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 171 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 171 237
  (Polychromatic418967fa.accept_10_4_1_7_1_371 64 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 171 237 3 21 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 171 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 171 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 171 237 (Polychromatic418967fa.accept_12_1_3_9_1_174
  61 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 171 237 3 20 57 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 171 237
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 59 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 171 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 171 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 171 237 3 19 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 171 237 (Polychromatic418967fa.accept_10_6_1_7_1_342
  56 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 237
  (Polychromatic418967fa.accept_12_7_3_9_1_999 55 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 171 237 3 18 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 171 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 171 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 171 237
  (Polychromatic418967fa.accept_14_10_3_13_1_1530 52 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 171 237 3 17 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 171 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 171 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 237
  (Polychromatic418967fa.accept_12_1_3_9_1_174 49 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 171 237 3 16 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 171 237 (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 171 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 171 237 3 15 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 171 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 171 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 237 (Polychromatic418967fa.accept_12_7_3_9_1_999
  43 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 171 237 3 14 57 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 171 237
  (Polychromatic418967fa.accept_12_5_3_9_1_541 41 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 171 237 (Polychromatic418967fa.accept_13_1_2_3_1_911 40 171 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 171 237 3 13 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 171 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 38
  171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 171 237 3 12 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 171 237 (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 171 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 171 237 3 11 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 171 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 171 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 237 (Polychromatic418967fa.accept_12_7_3_9_1_999
  31 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 171 237 3 10 57 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 171 237
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 171 237 (Polychromatic418967fa.accept_20_8_11_17_1_12889 28 171 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 171 237 3 9 57 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 171 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 171 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 171 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 171 237 3 8 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 171 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 23
  171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 171 237 3 7 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 171 237 (Polychromatic418967fa.accept_15_5_6_12_1_916 20 171 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 237 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 171
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 171 237 3 6 57 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 171 237
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 171 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 171 237 3 5 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 171 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14
  171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 237
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 171 237 3 4 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 171 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 171 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 171 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 171 237 3 3 57 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 171 237
  (Polychromatic418967fa.accept_16_8_11_13_1_7265 8 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 171 237 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 171 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 171 237 3 2 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 171 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 171 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 4 171 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 171 237 3 1 57 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 171 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 171 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 171 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 170 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 170 237 (accept_3_4 67 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 170 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 170 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 170 237 (accept_3_4 64 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 170 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 170 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 170 237
  (Polychromatic418967fa.accept_15_2_5_12_1_369 62 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 170 237 (accept_3_4 61 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 170 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 170 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 170 237 (accept_3_4 58 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 170 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 170 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 170 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 170 237 (accept_3_4 55 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 170 237 (Polychromatic418967fa.accept_11_10_5_6_1_1842 54 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 170 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 170 237 (accept_3_4 52 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 170 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 170 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 170 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 170 237 (accept_3_4 49 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 170 237 (Polychromatic418967fa.accept_18_12_8_3_1_1627 48 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 170 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 170 237 (accept_3_4 46 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 170 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 170 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 170 237
  (Polychromatic418967fa.accept_13_5_1_3_1_878 44 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 170 237 (accept_3_4 43 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 170 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 170 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 170 237 (accept_3_4 40 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 170 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 170 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 170 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 170 237 (accept_3_4 37 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 170 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 170 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 170 237 (accept_3_4 34 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 170 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 170 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 170 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 170 237 (accept_3_4 31 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 170 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 170 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 170 237 (accept_3_4 28 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 170 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 170 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 170 237
  (Polychromatic418967fa.accept_27_26_8_21_1_12384 26 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 170 237 (accept_3_4 25 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 170 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 170 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 170 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 170 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 170 237 (accept_3_4 22 170 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 170 237
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 170 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 170 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 170 237 (accept_3_4 19 170 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 170 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 170 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17
  170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 170 237 (accept_3_4 16
  170 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 170 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 170 237 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 170 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 170 237 (accept_3_4 13 170 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 170 237 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 170 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 170 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 170 237 (accept_3_4 10 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  170 237 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 170 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 170 237 (accept_3_4 7 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 170 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 170 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 170 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 170 237 (accept_3_4 4 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  170 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 170 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 170 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 170 237 (accept_3_4 1 170 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 170 237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  69 169 237 (Eq.refl Bool.true) (allA_succ_of_accept 68 169 237 (accept_3_5 68 169 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 169 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 67 169 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 169 237
  (Polychromatic418967fa.accept_18_12_7_3_1_2666 66 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 169 237 (accept_3_5 65 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 169 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 169 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 63 169 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 169 237 (accept_3_5 62 169 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 169 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 169 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 169 237
  (Polychromatic418967fa.accept_8_4_1_5_1_186 60 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 169 237 (accept_3_5 59 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 169 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 169 237 (Polychromatic418967fa.accept_11_2_4_6_1_2412 57 169 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 169 237 (accept_3_5 56 169 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 169 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 169 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 169 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 169 237 (accept_3_5 53 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 169 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 169 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 169 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 169 237 (accept_3_5 50 169 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 169 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 169 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 169 237
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 169 237 (accept_3_5 47 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 169 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 169 237 (Polychromatic418967fa.accept_18_9_7_3_1_3871 45 169 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 169 237 (accept_3_5 44 169 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 169 237 (Polychromatic418967fa.accept_25_18_19_12_1_14185 43
  169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 169 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 169 237 (accept_3_5 41 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 169 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 169 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 39 169 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 169 237 (accept_3_5 38 169 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 169 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 169 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 169 237
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 169 237 (accept_3_5 35 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 169 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 169 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 169 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 169 237 (accept_3_5 32 169 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 169 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 169 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 169 237 (accept_3_5 29 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 169 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 169 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 169 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 237 (accept_3_5 26 169 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 169 237 (Polychromatic418967fa.accept_19_6_17_9_1_10318 25 169
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 169 237 (accept_3_5 23 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 237 (Polychromatic418967fa.accept_14_7_1_13_1_357 21 169 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 237 (accept_3_5 20 169 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 169 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 237
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 237 (accept_3_5 17 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 169 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 169 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 237 (accept_3_5 14 169 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 169 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 237 (accept_3_5 11 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 169 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 237 (accept_3_5 8 169 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 237 (Polychromatic418967fa.accept_14_7_1_13_1_357 7 169 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 237 (accept_3_5 5 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 169 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 169 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 237 (accept_3_5 2 169 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 169 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 168 237 (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 168 237 3 23 56 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 168 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 68 168 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 168 237 (Polychromatic418967fa.accept_9_4_6_3_1_179
  67 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 168 237 3 22 56 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 168 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 65 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 168 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 64 168 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 168 237 3 21 56 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 168 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 62
  168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 168 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 61 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 168 237 3 20 56 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 168 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 59 168 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 168 237 (Polychromatic418967fa.accept_9_4_6_3_1_179
  58 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 168 237 3 19 56 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 168 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 56 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 168 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 55 168 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 168 237 3 18 56 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 168 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 53
  168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 168 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 52 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 168 237 3 17 56 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 168 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 168 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 168 237 (Polychromatic418967fa.accept_9_4_6_3_1_179
  49 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 168 237 3 16 56 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 168 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 47 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 168 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 46 168 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 168 237 3 15 56 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 168 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 44
  168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 168 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 237 3 14 56 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 168 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 168 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 168 237 (Polychromatic418967fa.accept_9_4_6_3_1_179
  40 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 168 237 3 13 56 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 168 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 168 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 168 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 168 237 3 12 56 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 168 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 168 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 168 237 3 11 56 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 168 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 168 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 168 237 (Polychromatic418967fa.accept_9_4_6_3_1_179
  31 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 168 237 3 10 56 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 168 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 168 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 168 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 168 237 3 9 56 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 168 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 26
  168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 237 3 8 56 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 168 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 168 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 168 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 168 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 168 237 3 7 56 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 168 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 168 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 168 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 168 237 3 6 56 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 168 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 17
  168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 168 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 168 237 3 5 56 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 168 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 168 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 168 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 168 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 237 3 4 56 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 168 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 168 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 168 237 3 3 56 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 168 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 168 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 168 237 3 2 56 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 168 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 168 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 168 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 168 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 168 237 3 1 56 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 168 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 168 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 168 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 168 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 168
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 167 237 (Eq.refl Bool.true)
  (allA_succ_of_accept 70 167 237 (accept_3_4 70 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 167 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 167 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 167 237 (accept_3_4 67 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 167 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 167 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 167 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 65 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 167 237 (accept_3_4 64 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 167 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 167 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 167 237 (accept_3_4 61 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 167 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 167 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 167 237
  (Polychromatic418967fa.accept_11_4_2_6_1_389 59 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 167 237 (accept_3_4 58 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 167 237 (Polychromatic418967fa.accept_13_5_11_3_1_902 57 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 167 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 167 237 (accept_3_4 55 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 167 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 167 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 167 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 53 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 167 237 (accept_3_4 52 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 167 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 167 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 167 237 (accept_3_4 49 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 167 237 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 167 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 167 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 167 237 (accept_3_4 46 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 167 237 (Polychromatic418967fa.accept_17_11_14_16_1_1270 45 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 44 167 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 167 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 167 237 (accept_3_4 43 167 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 167 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 167 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 167 237
  (Polychromatic418967fa.accept_13_2_11_3_1_873 41 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 167 237 (accept_3_4 40 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 167 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 167 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 167 237 (accept_3_4 37 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 167 237 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 167 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 167 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 167 237 (accept_3_4 34 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 167 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 167 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 167 237 (accept_3_4 31 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 167 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 167 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 167 237 (accept_3_4 28 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 167 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 167 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 237 (accept_3_4 25 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 167 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 167 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 237
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 23 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 167 237 (accept_3_4 22 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 167 237 (Polychromatic418967fa.accept_13_8_11_3_1_3053 21 167 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 167 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 237 (accept_3_4 19 167 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 167 237 (accept_3_4 16 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 237 (accept_3_4 13 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 237 (Polychromatic418967fa.accept_20_12_7_17_1_12857 12 167 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 237 (accept_3_4 10 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 237 (Polychromatic418967fa.accept_16_9_7_13_1_4997 9 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 237 (accept_3_4 7 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 167 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 237
  (Polychromatic418967fa.accept_13_5_11_3_1_902 5 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 237 (accept_3_4 4 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 167 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 237 (accept_3_4 1 167 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167 237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 72 166 237 (Eq.refl Bool.true) (allA_succ_of_accept 71 166 237 (accept_3_5 71 166 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 166 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 166 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 166 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 69 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 166 237 (accept_3_5 68 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 166 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 166 237 (Polychromatic418967fa.accept_12_6_10_9_1_531 66 166 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 166 237 (accept_3_5 65 166 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 166 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 166 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 166 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 166 237 (accept_3_5 62 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 166 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 166 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 166 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 166 237 (accept_3_5 59 166 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 166 237 (Polychromatic418967fa.accept_13_6_10_3_1_897 58 166 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 166 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 166 237 (accept_3_5 56 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 166 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 166 237 (Polychromatic418967fa.accept_12_6_10_9_1_531 54 166 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 166 237 (accept_3_5 53 166 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 166 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 166 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 166 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 166 237 (accept_3_5 50 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 166 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 166 237 (Polychromatic418967fa.accept_14_6_12_13_1_3180 48 166 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 166 237 (accept_3_5 47 166 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 166 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 166 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 166 237
  (Polychromatic418967fa.accept_13_6_10_3_1_897 45 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 166 237 (accept_3_5 44 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 166 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 166 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 166 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 166 237 (accept_3_5 41 166 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 166 237 (Polychromatic418967fa.accept_11_7_1_6_1_1281 40 166 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 166 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 166 237 (accept_3_5 38 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 166 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 166 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 166 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 166 237 (accept_3_5 35 166 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 166 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 166 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 166 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 166 237 (accept_3_5 32 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 166 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 166 237 (Polychromatic418967fa.accept_12_6_10_9_1_531 30 166 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 166 237 (accept_3_5 29 166 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 166 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 166 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 166 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 166 237 (accept_3_5 26 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 166 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 166 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 166 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 166 237 (accept_3_5 23 166 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 166 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 166 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 166 237
  (Polychromatic418967fa.accept_10_1_6_7_1_710 21 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 166 237 (accept_3_5 20 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 166 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 166 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 166 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 166 237 (accept_3_5 17 166 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 166 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 166 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 166 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 166 237 (accept_3_5 14 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 166 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 166 237 (Polychromatic418967fa.accept_17_12_13_16_1_3226 12 166 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 166 237 (accept_3_5 11 166 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 166 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 166 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 166 237
  (Polychromatic418967fa.accept_16_9_6_13_1_3831 9 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 166 237 (accept_3_5 8 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  166 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 166 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 166 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 166 237 (accept_3_5 5 166 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 166 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 166 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 166 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 166 237 (accept_3_5 2 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  166 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 166 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 166 237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73
  165 237 (Eq.refl Bool.true) (allA_succ_of_gcd 72 165 237 3 24 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 165 237 (Polychromatic418967fa.accept_13_6_9_3_1_915 71 165 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 165 237
  (Polychromatic418967fa.accept_13_5_9_3_1_870 70 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 165 237 3 23 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 165 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 68 165 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 165 237 (Polychromatic418967fa.accept_13_2_9_3_1_2212
  67 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 165 237 3 22 55 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 165 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 65 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 165 237 (Polychromatic418967fa.accept_13_12_9_3_1_3047 64 165 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 165 237 3 21 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 165 237 (Polychromatic418967fa.accept_10_2_5_7_1_1124
  62 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 61 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 165 237 3 20 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 165 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 165 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 165 237 (Polychromatic418967fa.accept_7_2_4_6_1_166
  58 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 165 237 3 19 55 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 165 237
  (Polychromatic418967fa.accept_16_8_5_13_1_1021 56 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 165 237 (Polychromatic418967fa.accept_19_17_13_9_1_5970 55 165 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 165 237 3 18 55 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 165 237
  (Polychromatic418967fa.accept_10_3_5_7_1_330 53 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 165 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 165 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 165 237 3 17 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 165 237 (Polychromatic418967fa.accept_16_2_5_13_1_3842
  50 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 237
  (Polychromatic418967fa.accept_16_1_5_13_1_1025 49 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 165 237 3 16 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 165 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 165 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 237 (Polychromatic418967fa.accept_13_7_9_3_1_1504
  46 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 165 237 3 15 55 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 165 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 165 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 43 165 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 165 237 3 14 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 165 237 (Polychromatic418967fa.accept_13_2_9_3_1_2212
  41 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 40 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 165 237 3 13 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 165 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 165 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 237 (Polychromatic418967fa.accept_7_2_4_6_1_166
  37 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 165 237 3 12 55 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 165 237
  (Polychromatic418967fa.accept_17_1_12_16_1_2211 35 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 165 237 (Polychromatic418967fa.accept_13_8_9_3_1_2213 34 165 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 165 237 3 11 55 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 165 237
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 165 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 165 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 165 237 3 10 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 165 237
  (Polychromatic418967fa.accept_19_10_13_9_1_4552 29 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 165 237 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 165 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 165 237 3 9 55 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 165 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 165 237 (Polychromatic418967fa.accept_13_12_9_3_1_3047 25 165 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 165 237 3 8 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 165 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 23
  165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 237
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 22 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 165 237 3 7 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 165 237 (Polychromatic418967fa.accept_13_7_9_3_1_1504 20 165 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 165 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 165 237 3 6 55 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 165 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 165 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 237 3 5 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 237
  (Polychromatic418967fa.accept_21_14_18_6_1_12747 14 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 165 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 165 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 165 237 3 4 55 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 165 237
  (Polychromatic418967fa.accept_17_11_12_16_1_3219 11 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 165 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 165 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 165 237 3 3 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 165 237 (Polychromatic418967fa.accept_10_8_5_7_1_358 8
  165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 237
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 165 237 3 2 55 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 165 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 165 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 237 (Polychromatic418967fa.accept_19_4_13_9_1_5968 4 165
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 165 237 3 1 55 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 165 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 165 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 237 (Polychromatic418967fa.accept_16_1_5_13_1_1025 1 165 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 165
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 164 237 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 164 237 (accept_3_4 73 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 164 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 164 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 164 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 164 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 164 237 (accept_3_4 70 164 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 164 237 (Polychromatic418967fa.accept_9_6_2_3_1_771
  69 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 164 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 68 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 164 237 (accept_3_4 67 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 164 237 (Polychromatic418967fa.accept_12_6_8_9_1_553 66 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 164 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 164 237 (accept_3_4 64 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 164 237 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 164 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 164 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 62 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 164 237 (accept_3_4 61 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 164 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 164 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 164 237 (accept_3_4 58 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 164 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 164 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 164 237
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 56 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 164 237 (accept_3_4 55 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 164 237 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 164 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 164 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 164 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 164 237 (accept_3_4 52 164 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 164 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 51
  164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 164 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 50 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 164 237 (accept_3_4 49 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 164 237 (Polychromatic418967fa.accept_13_9_8_3_1_3045 48 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 164 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 164 237 (accept_3_4 46 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 164 237 (Polychromatic418967fa.accept_14_3_10_13_1_339 45 164 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 164 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 164 237 (accept_3_4 43 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 164 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 164 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 164 237 (accept_3_4 40 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 164 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 164 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 164 237
  (Polychromatic418967fa.accept_11_5_10_6_1_793 38 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 164 237 (accept_3_4 37 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 164 237 (Polychromatic418967fa.accept_21_15_17_6_1_6661 36 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 164 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 164 237 (accept_3_4 34 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 164 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 164 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 164 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 164 237 (accept_3_4 31 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 164 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 164 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 164 237 (accept_3_4 28 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 164 237 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 164 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 164 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 164 237 (accept_3_4 25 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 164 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 164 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 164 237 (accept_3_4 22 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 164 237 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 164 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 164 237
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 164 237 (accept_3_4 19 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 164 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 164 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 164 237 (accept_3_4 16 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 164 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 164 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 164 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 164 237 (accept_3_4 13 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 164 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 164 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 164 237 (accept_3_4 10 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 164 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 164 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 164 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 164 237 (accept_3_4 7 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  164 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 164 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 164 237 (accept_3_4 4 164 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 164 237 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 164 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 164 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 164 237 (accept_3_4 1 164 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 163 237 (Eq.refl
  Bool.true) (allA_succ_of_accept 74 163 237 (accept_3_5 74 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 163 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 163 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 163 237 (Polychromatic418967fa.accept_16_8_3_13_1_7295 72 163
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 163 237 (accept_3_5 71 163
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 163 237 (Polychromatic418967fa.accept_4_2_3_1_1_2
  70 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 163 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 69 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 163 237 (accept_3_5 68 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 163 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 163 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 163 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 163 237 (accept_3_5 65 163 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 163 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 163 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 163 237
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 63 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 163 237 (accept_3_5 62 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 163 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 61 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 163 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 163 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 163 237 (accept_3_5 59 163 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 163 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 163 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 163 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 163 237 (accept_3_5 56 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 163 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 55 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 163 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 163 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 163 237 (accept_3_5 53 163 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 163 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 163 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 163 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 51 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 163 237 (accept_3_5 50 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 163 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 163 237 (Polychromatic418967fa.accept_13_9_7_3_1_1531 48 163 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 163 237 (accept_3_5 47 163 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 163 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 163 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 163 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 163 237 (accept_3_5 44 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 163 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 163 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 163 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 163 237 (accept_3_5 41 163 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 163 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 163 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 163 237 (accept_3_5 38 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 163 237 (Polychromatic418967fa.accept_13_11_7_3_1_894 37 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 163 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 163 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 237 (accept_3_5 35 163 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 163 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 163 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 33 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 163 237 (accept_3_5 32 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 163 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 163 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 163 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 237 (accept_3_5 29 163 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 163 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 237
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 237 (accept_3_5 26 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 163 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 163 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 237 (accept_3_5 23 163 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 163 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 237
  (Polychromatic418967fa.accept_13_8_7_3_1_430 21 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 237 (accept_3_5 20 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 237 (Polychromatic418967fa.accept_29_19_18_5_1_14184 19 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 163 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 237 (accept_3_5 17 163 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 163 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 237 (accept_3_5 14 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 237 (Polychromatic418967fa.accept_18_12_1_3_1_7843 12 163 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 237 (accept_3_5 11 163 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 163 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 237
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 237 (accept_3_5 8 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 163 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 237 (accept_3_5 5 163 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 163 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 237 (accept_3_5 2 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 163 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  76 162 237 (Eq.refl Bool.true) (allA_succ_of_gcd 75 162 237 3 25 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 162 237 (Polychromatic418967fa.accept_10_4_2_7_1_373
  74 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 162 237
  (Polychromatic418967fa.accept_19_16_10_9_1_8842 73 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 162 237 3 24 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 162 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 162 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 162 237
  (Polychromatic418967fa.accept_12_10_6_9_1_549 70 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 162 237 3 23 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 162 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 162 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 162 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 67
  162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 162 237 3 22 54 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 162 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 162 237 (Polychromatic418967fa.accept_10_4_2_7_1_373 64 162 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 162 237 3 21 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 162 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 62
  162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 162 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 162 237 3 20 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 162 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 162 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 162 237 (Polychromatic418967fa.accept_7_2_1_6_1_173
  58 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 162 237 3 19 54 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 162 237
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 56 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 162 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 162 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 162 237 3 18 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 162 237 (Polychromatic418967fa.accept_13_1_6_3_1_1547
  53 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 162 237
  (Polychromatic418967fa.accept_12_4_6_9_1_548 52 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 162 237 3 17 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 162 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 50 162 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 162 237 (Polychromatic418967fa.accept_10_9_2_7_1_1096
  49 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 162 237 3 16 54 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 162 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 162 237 (Polychromatic418967fa.accept_12_10_6_9_1_549 46 162 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 162 237 3 15 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 162 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 44
  162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 162 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 237 3 14 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 162 237 (Polychromatic418967fa.accept_19_3_10_9_1_7338 41 162 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 162 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 40 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 162 237 3 13 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 162 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 38 162 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 162 237 (Polychromatic418967fa.accept_7_2_1_6_1_173
  37 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 162 237 3 12 54 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 162 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 162 237 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 162 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 162 237 3 11 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 162 237 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  32 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 237 3 10 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 237 (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 162 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 162 237
  (Polychromatic418967fa.accept_12_4_6_9_1_548 28 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 162 237 3 9 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 162 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 162 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 162 237 (Polychromatic418967fa.accept_10_5_2_7_1_345 25 162
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 162 237 3 8 54 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 162 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 162 237 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 162 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 162 237 3 7 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 162 237 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  20 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 237 3 6 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 162 237 (Polychromatic418967fa.accept_21_17_15_6_1_3557 17 162 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 162 237 (Polychromatic418967fa.accept_7_2_1_6_1_173
  16 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 162 237 3 5 54 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 162 237
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 162 237 (Polychromatic418967fa.accept_17_13_9_16_1_3254 13 162 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 162 237 3 4 54 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 162 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 162 237 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 162 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 162 237 3 3 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 162 237 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 162 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 237 3 2 54 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 162 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 162 237 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 162 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 162 237 3 1 54 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 162 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 162 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 162 237 (Polychromatic418967fa.accept_13_1_6_3_1_1547 1 162 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 162
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 161 237 (Eq.refl
  Bool.true) (allA_succ_of_accept 76 161 237 (accept_3_4 76 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 161 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 75 161 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 161 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 161 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 161 237 (accept_3_4 73 161 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 161 237
  (Polychromatic418967fa.accept_21_9_14_6_1_11308 72 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 161 237 (Polychromatic418967fa.accept_13_6_5_3_1_426 71 161 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 161 237 (accept_3_4 70 161 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 161 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 161 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 161 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 161 237 (accept_3_4 67 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 161 237 (Polychromatic418967fa.accept_10_6_1_7_1_342 66 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 161 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 65 161 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 237 (accept_3_4 64 161 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 161 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 161 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 161 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 161 237 (accept_3_4 61 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 161 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 161 237 (Polychromatic418967fa.accept_9_5_8_3_1_437 59 161 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 237 (accept_3_4 58 161 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 161 237 (Polychromatic418967fa.accept_14_1_7_13_1_333 57 161 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 161 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 161 237 (accept_3_4 55 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 161 237 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 161 237 (Polychromatic418967fa.accept_13_1_5_3_1_888 53 161 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 237 (accept_3_4 52 161 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 161 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 161 237 (accept_3_4 49 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 161 237 (Polychromatic418967fa.accept_13_9_5_3_1_428 48 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 161 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 161 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 237 (accept_3_4 46 161 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 237 (Polychromatic418967fa.accept_11_1_7_6_1_378 45 161 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 161 237 (accept_3_4 43 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 161 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 161 237 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 161 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 237 (accept_3_4 40 161 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 161 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 237 (accept_3_4 37 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 161 237 (Polychromatic418967fa.accept_13_9_5_3_1_428 35 161 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 237 (accept_3_4 34 161 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 161 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 237 (accept_3_4 31 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 237 (Polychromatic418967fa.accept_16_14_1_13_1_2754 30 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 161 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 237 (accept_3_4 28 161 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 161 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 237 (accept_3_4 25 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 237 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 161 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 237 (accept_3_4 22 161 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 237 (Polychromatic418967fa.accept_13_8_5_3_1_427 21 161 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 237 (accept_3_4 19 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 237 (Polychromatic418967fa.accept_20_18_1_17_1_4085 18 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 237 (Polychromatic418967fa.accept_27_17_26_21_1_14183 17 161 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 237 (accept_3_4 16 161 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 161 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 237 (accept_3_4 13 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 161 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 237 (accept_3_4 10 161 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 237 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 161 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 237 (accept_3_4 7 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 237 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 161 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 237 (accept_3_4 4 161 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 161 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 237 (accept_3_4 1 161 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 160 237 (Eq.refl
  Bool.true) (allA_succ_of_accept 77 160 237 (accept_3_5 77 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 160 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 76 160 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 160 237 (Polychromatic418967fa.accept_14_5_6_13_1_3145 75 160
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 160 237 (accept_3_5 74 160
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 160 237
  (Polychromatic418967fa.accept_6_1_4_3_1_14 73 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 160 237 (Polychromatic418967fa.accept_13_7_4_3_1_3064 72 160 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 160 237 (accept_3_5 71 160 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 160 237 (Polychromatic418967fa.accept_21_7_13_6_1_349 70 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 160 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 69 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 160 237 (accept_3_5 68 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 160 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 160 237 (Polychromatic418967fa.accept_12_6_4_9_1_544 66 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 160 237 (accept_3_5 65 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 160 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 64 160 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 160 237
  (Polychromatic418967fa.accept_14_7_6_13_1_4111 63 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 160 237 (accept_3_5 62 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 160 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 160 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 60 160 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 160 237 (accept_3_5 59 160 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 160 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 160 237
  (Polychromatic418967fa.accept_17_6_7_16_1_6836 57 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 160 237 (accept_3_5 56 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 160 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 160 237 (Polychromatic418967fa.accept_12_6_4_9_1_544 54 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 160 237 (accept_3_5 53 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 160 237 (Polychromatic418967fa.accept_15_7_10_12_1_2403 52 160
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 160 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 51 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 160 237 (accept_3_5 50 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 160 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 160 237 (Polychromatic418967fa.accept_22_4_6_17_1_9670 48 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 160 237 (accept_3_5 47 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 160 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 160 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 160 237
  (Polychromatic418967fa.accept_19_7_8_9_1_7322 45 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 160 237 (accept_3_5 44 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 160 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 160 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 160 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 160 237 (accept_3_5 41 160 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 160 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 160 237
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 160 237 (accept_3_5 38 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 160 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 160 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 160 237 (Polychromatic418967fa.accept_15_6_10_12_1_2538 36 160
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 160 237 (accept_3_5 35 160
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 160 237
  (Polychromatic418967fa.accept_22_12_6_17_1_11214 34 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 160 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 160 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 160 237 (accept_3_5 32 160 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 160 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 160 237
  (Polychromatic418967fa.accept_12_6_4_9_1_544 30 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 160 237 (accept_3_5 29 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 160 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 160 237 (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 160 237 (accept_3_5 26 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 160 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 160 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 160 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 160 237 (accept_3_5 23 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 160 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 160 237 (Polychromatic418967fa.accept_14_7_6_13_1_4111 21 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 160 237 (accept_3_5 20 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 160 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 160 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 160 237
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 160 237 (accept_3_5 17 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 160 237 (Polychromatic418967fa.accept_19_16_8_9_1_8858 16 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 160 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 160 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 160 237 (accept_3_5 14 160 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 160 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 160 237
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 160 237 (accept_3_5 11 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 160 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 160 237 (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 160 237 (accept_3_5 8 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 160 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 160 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 160 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 160 237 (accept_3_5 5 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  160 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 160 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 160 237 (Polychromatic418967fa.accept_17_3_7_16_1_3251 3 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 160 237 (accept_3_5 2 160 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 160 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 160 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 159 237 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 159 237 3 26 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 159 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 77 159 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 159 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 76 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 159 237 3 25 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 159 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 159 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 237 (Polychromatic418967fa.accept_9_1_6_3_1_177
  73 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 159 237 3 24 53 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 159 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 71 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 159 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 159 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 159 237 3 23 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 159 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 68
  159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 159 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 159 237 3 22 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 159 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 65 159 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 159 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 64
  159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 159 237 3 21 53 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 159 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 159 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 61 159 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 159 237 3 20 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 159 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 59
  159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 159 237 3 19 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 159 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 56 159 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 237 (Polychromatic418967fa.accept_9_1_6_3_1_177
  55 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 159 237 3 18 53 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 159 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 159 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 52 159 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 159 237 3 17 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 159 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 50
  159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 159 237 3 16 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 159 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 159 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 46
  159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 159 237 3 15 53 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 159 237
  (Polychromatic418967fa.accept_9_8_6_3_1_457 44 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 159 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 159 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 159 237 3 14 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 159 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 41
  159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 40 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 159 237 3 13 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 159 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 159 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 237 (Polychromatic418967fa.accept_9_1_6_3_1_177
  37 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 159 237 3 12 53 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 159 237
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 159 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 159 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 159 237 3 11 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 159 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 32
  159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 159 237 3 10 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 159 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 159 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 237 (Polychromatic418967fa.accept_9_1_6_3_1_177
  28 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 159 237 3 9 53 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 159 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 159 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 159 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 159 237 3 8 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 159 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 23
  159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 159 237 3 7 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 159 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 159 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 159 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 159 237 3 6 53 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 159 237
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 159 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 159 237 3 5 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 159 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14
  159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 159 237 3 4 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 159 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 159 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 159 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 237 3 3 53 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 159 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 159 237 3 2 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 159 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 159 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 4 159 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 159 237 3 1 53 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 159 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 159 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 159 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 158 237 (Eq.refl
  Bool.true) (allA_succ_of_gcd 79 158 237 79 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 78 158 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 78 158 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 158 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 77
  158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 158 237 (accept_3_4 76
  158 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 158 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 158 237 (Polychromatic418967fa.accept_9_2_5_3_1_37 74 158 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 158 237 (accept_3_4 73 158 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 158 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 158 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 158 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 71
  158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 158 237 (accept_3_4 70
  158 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 158 237
  (Polychromatic418967fa.accept_9_6_5_3_1_205 69 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 158 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 68 158 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 158 237 (accept_3_4 67 158 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 158 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 158 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 158 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 65
  158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 158 237 (accept_3_4 64
  158 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 158 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 158 237 (Polychromatic418967fa.accept_9_8_5_3_1_777 62 158 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 158 237 (accept_3_4 61 158 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 158 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 158 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 158 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 59
  158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 158 237 (accept_3_4 58
  158 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 158 237
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 57 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 158 237 (Polychromatic418967fa.accept_9_2_5_3_1_37 56 158 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 158 237 (accept_3_4 55 158 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 158 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 158 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 158 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 53
  158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 158 237 (accept_3_4 52
  158 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 158 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 158 237 (Polychromatic418967fa.accept_13_11_2_3_1_883 50 158 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 158 237 (accept_3_4 49 158 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 158 237 (Polychromatic418967fa.accept_13_9_2_3_1_3027 48 158 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 158 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 158 237 (accept_3_4 46 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 158 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 158 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 158 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 158 237 (accept_3_4 43 158 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 158 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 158 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 158 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 158 237 (accept_3_4 40 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 158 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 158 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 158 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 158 237 (accept_3_4 37 158 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 158 237 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 158 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 158 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 158 237 (accept_3_4 34 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 158 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 158 237 (Polychromatic418967fa.accept_19_13_6_9_1_5989 32 158 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 158 237 (accept_3_4 31 158 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 158 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 158 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 158 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 158 237 (accept_3_4 28 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 158 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 158 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 158 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 158 237 (accept_3_4 25 158 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 158 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 158 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 158 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 158 237 (accept_3_4 22 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 158 237 (Polychromatic418967fa.accept_17_4_5_16_1_3240 21 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 158 237 (Polychromatic418967fa.accept_9_2_5_3_1_37 20 158 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 158 237 (accept_3_4 19 158 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 158 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 158 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 158 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 158 237 (accept_3_4 16 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 158 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 158 237 (Polychromatic418967fa.accept_13_1_2_3_1_911 14 158 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 158 237 (accept_3_4 13 158 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 158 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 158 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 158 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 158 237 (accept_3_4 10 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  158 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 158 237 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 158 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 158 237 (accept_3_4 7 158 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 158 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 158 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 158 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 158 237 (accept_3_4 4 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  158 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 158 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 158 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 158 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 158 237 (accept_3_4 1 158 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 158 237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 81 157 237 (Eq.refl Bool.true) (allA_succ_of_accept 80 157 237 (accept_3_5 80 157 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 157 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 79 157 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 157 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 78 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 157 237 (accept_3_5 77 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 157 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 157 237 (Polychromatic418967fa.accept_11_9_3_6_1_797 75 157 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 157 237 (accept_3_5 74 157 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 157 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 73 157 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 157 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 157 237 (accept_3_5 71 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 157 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 157 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 69 157 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 157 237 (accept_3_5 68 157 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 157 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 157 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 157 237
  (Polychromatic418967fa.accept_14_10_3_13_1_1530 66 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 157 237 (accept_3_5 65 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 157 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 157 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 157 237 (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 157
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 157 237 (accept_3_5 62 157
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 157 237
  (Polychromatic418967fa.accept_9_7_4_3_1_204 61 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 157 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 157 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 157 237 (accept_3_5 59 157 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 157 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 157 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 157 237 (Polychromatic418967fa.accept_13_5_1_3_1_878
  57 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 157 237 (accept_3_5 56
  157 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 157 237
  (Polychromatic418967fa.accept_9_1_4_3_1_201 55 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 157 237 (Polychromatic418967fa.accept_13_2_1_3_1_419 54 157 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 237 (accept_3_5 53 157 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 157 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 157 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 157 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 51
  157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 157 237 (accept_3_5 50
  157 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 157 237
  (Polychromatic418967fa.accept_15_4_7_12_1_5538 49 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 157 237 (Polychromatic418967fa.accept_15_3_7_12_1_372 48 157 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 237 (accept_3_5 47 157 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 157 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 157 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 237 (Polychromatic418967fa.accept_13_6_1_3_1_1522
  45 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 157 237 (accept_3_5 44
  157 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 157 237
  (Polychromatic418967fa.accept_9_7_4_3_1_204 43 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 157 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 157 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 237 (accept_3_5 41 157 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 157 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 157 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 237 (Polychromatic418967fa.accept_7_4_3_6_1_340
  39 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 157 237 (accept_3_5 38
  157 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 157 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 157 237 (Polychromatic418967fa.accept_15_6_7_12_1_869 36 157 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 237 (accept_3_5 35 157 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 157 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 157 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 237 (Polychromatic418967fa.accept_9_6_4_3_1_203
  33 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 157 237 (accept_3_5 32
  157 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 157 237
  (Polychromatic418967fa.accept_11_9_3_6_1_797 31 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 157 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 157 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 237 (accept_3_5 29 157 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 157 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 157 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 237 (Polychromatic418967fa.accept_12_3_1_9_1_202
  27 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 157 237 (accept_3_5 26
  157 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 157 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 157 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 237 (accept_3_5 23 157 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 157 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 157 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 237 (Polychromatic418967fa.accept_15_6_7_12_1_869
  21 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 237 (accept_3_5 20
  157 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 237
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 157 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 157 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 237 (accept_3_5 17 157 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 157 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 157 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 237 (Polychromatic418967fa.accept_9_6_4_3_1_203
  15 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 237 (accept_3_5 14
  157 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 237
  (Polychromatic418967fa.accept_19_13_5_9_1_3318 13 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 157 237 (Polychromatic418967fa.accept_18_12_13_3_1_6427 12 157 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 237 (accept_3_5 11 157 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 157 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 237 (accept_3_5 8 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 157 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 237 (accept_3_5 5 157 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 157 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 237
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 237 (accept_3_5 2 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 157 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 82 156 237 (Eq.refl Bool.true) (allA_succ_of_gcd 81 156 237 3 27 52 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 156 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 80 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 156 237 (Polychromatic418967fa.accept_16_15_12_13_1_1045 79 156 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 156 237 3 26 52 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 156 237
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 77 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 156 237 (Polychromatic418967fa.accept_21_13_9_6_1_1190 76 156 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 156 237 3 25 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 156 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 74
  156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 156 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 73 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 156 237 3 24 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 156 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 156 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 156 237 (Polychromatic418967fa.accept_11_4_2_6_1_389
  70 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 156 237 3 23 52 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 156 237
  (Polychromatic418967fa.accept_16_4_12_13_1_990 68 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 156 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 156 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 156 237 3 22 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 156 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 65
  156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 156 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 64 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 156 237 3 21 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 156 237 (Polychromatic418967fa.accept_15_2_6_12_1_1613 62 156 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 156 237
  (Polychromatic418967fa.accept_10_1_6_7_1_710 61 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 237 3 20 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 156 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 156 237
  (Polychromatic418967fa.accept_16_10_12_13_1_4950 58 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 57 156 237 3 19 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 56 156 237 (Polychromatic418967fa.accept_16_8_12_13_1_3851 56 156 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 156 237
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 55 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 156 237 3 18 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 156 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 156 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 156 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 52 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 156 237 3 17 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 156 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 156 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 156 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 49
  156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 156 237 3 16 52 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 156 237
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 47 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 156 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 156 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 156 237 3 15 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 156 237 (Polychromatic418967fa.accept_18_8_12_3_1_2708
  44 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 156 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 237 3 14 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 156 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 156 237
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 40 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 156 237 3 13 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 156 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 156 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 156 237
  (Polychromatic418967fa.accept_11_4_2_6_1_389 37 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 237 3 12 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 156 237 (Polychromatic418967fa.accept_15_5_6_12_1_916 35 156 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 156 237
  (Polychromatic418967fa.accept_19_15_4_9_1_11608 34 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 156 237 3 11 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 156 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 156 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 237 3 10 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 156 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 156 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 156 237 (Polychromatic418967fa.accept_21_7_9_6_1_8212
  28 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 156 237 3 9 52 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 156 237
  (Polychromatic418967fa.accept_11_4_2_6_1_389 26 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 156 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 156 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 237 3 8 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 237 (Polychromatic418967fa.accept_10_3_6_7_1_2188
  23 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 156 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 22 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 156 237 3 7 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 156 237 (Polychromatic418967fa.accept_15_5_6_12_1_916 20 156 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 237 (Polychromatic418967fa.accept_18_1_12_3_1_6426 19 156
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 237 3 6 52 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 156 237 (Polychromatic418967fa.accept_19_16_4_9_1_10196 16 156 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 156 237 3 5 52 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 156 237
  (Polychromatic418967fa.accept_18_14_12_3_1_5103 14 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 156 237 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 156 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 237 3 4 52 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 156 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 156 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 156 237 3 3 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 156 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 156 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 237
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 156 237 3 2 52 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 156 237 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 156 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 156 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 156 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 156 237 3 1 52 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 156 237
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 2 156 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 156 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 156 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 156
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 155 237 (Eq.refl
  Bool.true) (allA_succ_of_accept 82 155 237 (accept_3_4 82 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 155 237 (Polychromatic418967fa.accept_15_6_5_12_1_1642 81 155 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 155 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 155 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 155 237 (accept_3_4 79 155 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 155 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 78
  155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 155 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 77 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 155 237 (accept_3_4 76 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 155 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 155 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 155 237 (accept_3_4 73 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 155 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 155 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 155 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 71 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 155 237 (accept_3_4 70 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 155 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 155 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 155 237 (accept_3_4 67 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 155 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 155 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 155 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 155 237 (accept_3_4 64 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 155 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 155 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 155 237 (accept_3_4 61 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 155 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 155 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 155 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 59 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 155 237 (accept_3_4 58 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 155 237 (Polychromatic418967fa.accept_21_15_8_6_1_5106 57 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 155 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 155 237 (accept_3_4 55 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 155 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 155 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 53 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 155 237 (accept_3_4 52 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 155 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 155 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 155 237 (accept_3_4 49 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 155 237 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 155 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 155 237 (accept_3_4 46 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 155 237 (Polychromatic418967fa.accept_20_5_15_17_1_7077 45 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 155 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 155 237 (accept_3_4 43 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 155 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 155 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 155 237 (accept_3_4 40 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 155 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 155 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 237 (accept_3_4 37 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 155 237 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 155 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 155 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 155 237 (accept_3_4 34 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 155 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 155 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 237 (accept_3_4 31 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 155 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 155 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 237
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 155 237 (accept_3_4 28 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 155 237 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 155 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 237 (accept_3_4 25 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 155 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 155 237 (accept_3_4 22 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 237 (Polychromatic418967fa.accept_14_7_1_13_1_357 21 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 155 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 237 (accept_3_4 19 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 155 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 237 (accept_3_4 16 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 237 (accept_3_4 13 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 155 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 237
  (Polychromatic418967fa.accept_19_11_3_9_1_8882 11 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 155 237 (accept_3_4 10 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  155 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 155 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 237 (accept_3_4 7 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 155 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 237 (accept_3_4 4 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 155 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 237 (accept_3_4 1 155 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 154 237 (Eq.refl
  Bool.true) (allA_succ_of_accept 83 154 237 (accept_3_5 83 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 154 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 82 154 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 154 237 (Polychromatic418967fa.accept_10_1_4_7_1_374 81 154
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 154 237 (accept_3_5 80 154
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 154 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 79 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 154 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 78 154 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 154 237 (accept_3_5 77 154 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 154 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 76 154 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 154 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 75
  154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 154 237 (accept_3_5 74
  154 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 154 237
  (Polychromatic418967fa.accept_6_1_4_3_1_14 73 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 154 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 154 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 154 237 (accept_3_5 71 154 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 154 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 70 154 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 154 237 (Polychromatic418967fa.accept_9_6_1_3_1_191
  69 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 154 237 (accept_3_5 68
  154 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 154 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 67 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 154 237 (Polychromatic418967fa.accept_12_6_10_9_1_531 66 154 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 154 237 (accept_3_5 65 154 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 154 237 (Polychromatic418967fa.accept_19_7_2_9_1_6006 64 154 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 154 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 154 237 (accept_3_5 62 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 154 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 154 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 60 154 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 154 237 (accept_3_5 59 154 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 154 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 58 154 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 154 237
  (Polychromatic418967fa.accept_13_5_11_3_1_902 57 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 154 237 (accept_3_5 56 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 154 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 154 237 (Polychromatic418967fa.accept_12_6_10_9_1_531 54 154 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 154 237 (accept_3_5 53 154 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 154 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 52 154 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 154 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 154 237 (accept_3_5 50 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 154 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 154 237 (Polychromatic418967fa.accept_29_19_9_5_1_14182 48 154 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 154 237 (accept_3_5 47 154 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 154 237 (Polychromatic418967fa.accept_13_7_11_3_1_1540 46 154
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 154 237
  (Polychromatic418967fa.accept_19_7_2_9_1_6006 45 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 154 237 (accept_3_5 44 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 154 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 154 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 154 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 154 237 (accept_3_5 41 154 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 154 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 40 154 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 154 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 154 237 (accept_3_5 38 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 154 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 154 237 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 154 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 154 237 (accept_3_5 35 154 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 154 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 154 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 154 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 33 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 154 237 (accept_3_5 32 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 154 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 154 237 (Polychromatic418967fa.accept_12_6_10_9_1_531 30 154 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 154 237 (accept_3_5 29 154 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 154 237 (Polychromatic418967fa.accept_13_2_11_3_1_873 28 154
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 154 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 154 237 (accept_3_5 26 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 154 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 154 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 154 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 154 237 (accept_3_5 23 154 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 154 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 154 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 154 237
  (Polychromatic418967fa.accept_10_1_4_7_1_374 21 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 154 237 (accept_3_5 20 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 154 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 154 237 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 154 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 154 237 (accept_3_5 17 154 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 154 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 154 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 154 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 154 237 (accept_3_5 14 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 154 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 154 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 154 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 154 237 (accept_3_5 11 154 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 154 237 (Polychromatic418967fa.accept_13_10_11_3_1_1518 10 154
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 154 237
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 9 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 154 237 (accept_3_5 8 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  154 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 154 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 154 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 154 237 (accept_3_5 5 154 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 154 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 154 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 154 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 154 237 (accept_3_5 2 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  154 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 154 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 154 237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 85 153 237 (Eq.refl Bool.true) (allA_succ_of_gcd 84 153 237 3 28 51 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 153 237
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 83 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 153 237 (Polychromatic418967fa.accept_11_5_10_6_1_793 82 153 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 153 237 3 27 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 153 237 (Polychromatic418967fa.accept_13_2_10_3_1_1538
  80 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 153 237
  (Polychromatic418967fa.accept_18_7_9_3_1_800 79 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 153 237 3 26 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 153 237 (Polychromatic418967fa.accept_15_2_3_12_1_891 77 153 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 237
  (Polychromatic418967fa.accept_8_4_1_5_1_186 76 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 153 237 3 25 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 153 237 (Polychromatic418967fa.accept_10_4_3_7_1_1110 74 153 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 153 237
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 73 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 153 237 3 24 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 153 237 (Polychromatic418967fa.accept_11_5_10_6_1_793 71 153 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 237
  (Polychromatic418967fa.accept_16_6_9_13_1_2751 70 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 153 237 3 23 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 153 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 68 153 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 153 237
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 67 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 153 237 3 22 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 153 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 65 153 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 237
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 64 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 153 237 3 21 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 153 237 (Polychromatic418967fa.accept_15_2_3_12_1_891 62 153 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 237
  (Polychromatic418967fa.accept_18_7_9_3_1_800 61 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 153 237 3 20 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 153 237 (Polychromatic418967fa.accept_13_7_10_3_1_1505 59 153 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 237
  (Polychromatic418967fa.accept_13_6_10_3_1_897 58 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 153 237 3 19 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 153 237 (Polychromatic418967fa.accept_10_6_3_7_1_2197 56 153 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 237
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 55 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 153 237 3 18 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 153 237 (Polychromatic418967fa.accept_15_8_3_12_1_1657 53 153 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 237
  (Polychromatic418967fa.accept_8_4_1_5_1_186 52 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 153 237 3 17 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 153 237 (Polychromatic418967fa.accept_13_11_10_3_1_3020 50 153 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 237
  (Polychromatic418967fa.accept_11_5_10_6_1_793 49 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 153 237 3 16 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 153 237 (Polychromatic418967fa.accept_15_2_3_12_1_891 47 153 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 237
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 46 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 153 237 3 15 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 153 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 153 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 237
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 43 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 153 237 3 14 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 153 237 (Polychromatic418967fa.accept_13_2_10_3_1_1538 41 153 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 237
  (Polychromatic418967fa.accept_19_2_1_9_1_10240 40 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 153 237 3 13 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 153 237 (Polychromatic418967fa.accept_11_5_10_6_1_793 38 153 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 237
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 37 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 153 237 3 12 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 153 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 153 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 237
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 34 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 153 237 3 11 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 153 237 (Polychromatic418967fa.accept_13_6_10_3_1_897 32 153 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 237
  (Polychromatic418967fa.accept_18_13_9_3_1_5114 31 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 153 237 3 10 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 153 237 (Polychromatic418967fa.accept_19_10_1_9_1_10161 29 153 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 237
  (Polychromatic418967fa.accept_8_4_1_5_1_186 28 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 153 237 3 9 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 153 237 (Polychromatic418967fa.accept_10_6_3_7_1_2197 26 153 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 153
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 153 237 3 8 51 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 153 237
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 237 (Polychromatic418967fa.accept_15_7_3_12_1_365 22 153 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 153 237 3 7 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 153 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 20
  153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 237
  (Polychromatic418967fa.accept_13_6_10_3_1_897 19 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 153 237 3 6 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 153 237 (Polychromatic418967fa.accept_15_2_3_12_1_891 17 153 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 237 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 153
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 153 237 3 5 51 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 153 237
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 14 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 153 237 (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 153 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 153 237 3 4 51 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 153 237
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 153 237 (Polychromatic418967fa.accept_19_10_1_9_1_10161 10 153 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 237 3 3 51 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 237
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 237 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 153 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 153 237 3 2 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 153 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 153 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 237
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 153 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 153 237 3 1 51 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 153 237 (Polychromatic418967fa.accept_13_2_10_3_1_1538 2 153 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 237 (Polychromatic418967fa.accept_16_1_9_13_1_1822 1 153
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 152 237
  (Eq.refl Bool.true) (allA_succ_of_accept 85 152 237 (accept_3_4 85 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 152 237 (Polychromatic418967fa.accept_10_4_2_7_1_373 84 152 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 152 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 152 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 152 237 (accept_3_4 82 152 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 152 237 (Polychromatic418967fa.accept_7_4_5_6_1_344
  81 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 152 237
  (Polychromatic418967fa.accept_11_3_9_6_1_105 80 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 152 237 (accept_3_4 79 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 152 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 152 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 152 237 (accept_3_4 76 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 152 237 (Polychromatic418967fa.accept_10_5_2_7_1_345 75 152 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 152 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 74 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 152 237 (accept_3_4 73 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 152 237 (Polychromatic418967fa.accept_13_7_9_3_1_1504 72 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 152 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 152 237 (accept_3_4 70 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 152 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 152 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 152 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 68 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 152 237 (accept_3_4 67 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 152 237 (Polychromatic418967fa.accept_12_6_8_9_1_553 66 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 152 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 152 237 (accept_3_4 64 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 152 237 (Polychromatic418967fa.accept_15_3_2_12_1_2469 63 152 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 152 237
  (Polychromatic418967fa.accept_14_6_12_13_1_3180 62 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 152 237 (accept_3_4 61 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 152 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 152 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 152 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 152 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 152 237 (accept_3_4 58 152 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 152 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 57
  152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 152 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 152 237 (accept_3_4 55 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 152 237 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 152 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 152 237 (accept_3_4 52 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 152 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 152 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 152 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 152 237 (accept_3_4 49 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 152 237 (Polychromatic418967fa.accept_14_6_12_13_1_3180 48 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 152 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 152 237 (accept_3_4 46 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 152 237 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 152 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 152 237
  (Polychromatic418967fa.accept_10_4_2_7_1_373 44 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 152 237 (accept_3_4 43 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 152 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 152 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 152 237 (accept_3_4 40 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 152 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 152 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 152 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 38 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 152 237 (accept_3_4 37 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 152 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 152 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 152 237 (accept_3_4 34 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 152 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 152 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 152 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 152 237 (accept_3_4 31 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 152 237 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 152 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 152 237 (accept_3_4 28 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 152 237 (Polychromatic418967fa.accept_16_11_8_13_1_3844 27 152 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 152 237
  (Polychromatic418967fa.accept_20_6_12_17_1_8581 26 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 152 237 (accept_3_4 25 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 152 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 152 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 152 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 152 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 152 237 (accept_3_4 22 152 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 152 237 (Polychromatic418967fa.accept_13_8_9_3_1_2213
  21 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 152 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 152 237 (accept_3_4 19 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 152 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 152 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 152 237 (accept_3_4 16 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 152 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 152 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 152 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 152 237 (accept_3_4 13 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 152 237 (Polychromatic418967fa.accept_13_12_9_3_1_3047 12 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 152 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 152 237 (accept_3_4 10 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 152 237 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 152 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 152 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 152 237 (accept_3_4 7 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  152 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 152 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 237 (accept_3_4 4 152 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 152 237 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 152 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 152 237 (accept_3_4 1 152 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 151 237
  (Eq.refl Bool.true) (allA_succ_of_accept 86 151 237 (accept_3_5 86 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 151 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 85 151 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 151 237 (Polychromatic418967fa.accept_10_4_1_7_1_371 84 151
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 151 237 (accept_3_5 83 151
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 151 237 (Polychromatic418967fa.accept_4_2_3_1_1_2
  82 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 151 237
  (Polychromatic418967fa.accept_18_9_7_3_1_3871 81 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 151 237 (accept_3_5 80 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 151 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 79 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 151 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 151 237 (accept_3_5 77 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 151 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 151 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 151 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 151 237 (accept_3_5 74 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 151 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 73 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 151 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 151 237 (accept_3_5 71 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 151 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 151 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 151 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 69 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 151 237 (accept_3_5 68 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 151 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 67 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 151 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 151 237 (accept_3_5 65 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 151 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 151 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 151 237
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 63 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 151 237 (accept_3_5 62 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 151 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 151 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 60 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 151 237 (accept_3_5 59 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 151 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 151 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 151 237
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 57 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 151 237 (accept_3_5 56 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 151 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 151 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 237 (accept_3_5 53 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 151 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 151 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 151 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 151 237 (accept_3_5 50 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 151 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 151 237 (Polychromatic418967fa.accept_13_9_8_3_1_3045 48 151 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 151 237 (accept_3_5 47 151 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 151 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 151 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 151 237 (accept_3_5 44 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 151 237 (Polychromatic418967fa.accept_15_13_1_12_1_1638 43 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 151 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 237 (accept_3_5 41 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 151 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 237
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 237 (accept_3_5 38 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 237 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 151 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 237 (accept_3_5 35 151 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 151 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 237 (accept_3_5 32 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 237 (accept_3_5 29 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 151 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 237
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 237 (accept_3_5 26 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 237 (Polychromatic418967fa.accept_11_3_8_6_1_788 25 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 237 (accept_3_5 23 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 151 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 237
  (Polychromatic418967fa.accept_17_4_15_16_1_3231 21 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 151 237 (accept_3_5 20 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 151 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 151 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 151 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 237 (accept_3_5 17 151 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 237 (accept_3_5 14 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 237 (accept_3_5 11 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 151 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 237 (accept_3_5 8 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 237 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 237 (accept_3_5 5 151 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 151 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 237 (accept_3_5 2 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 151 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 88 150 237 (Eq.refl Bool.true) (allA_succ_of_gcd 87 150 237 3 29 50 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 150 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 86 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 150 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 85 150 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 150 237 3 28 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 150 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 83
  150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 150 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 82 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 150 237 3 27 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 150 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 80 150 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 150 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 79
  150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 150 237 3 26 50 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 150 237
  (Polychromatic418967fa.accept_9_5_6_3_1_40 77 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 150 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 76 150 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 150 237 3 25 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 150 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 74
  150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 150 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 73 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 150 237 3 24 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 150 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 150 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 150 237 (Polychromatic418967fa.accept_9_7_6_3_1_456
  70 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 150 237 3 23 50 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 150 237
  (Polychromatic418967fa.accept_9_5_6_3_1_40 68 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 150 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 150 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 150 237 3 22 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 150 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 65
  150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 150 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 64 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 150 237 3 21 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 150 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 62 150 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 150 237 (Polychromatic418967fa.accept_9_7_6_3_1_456
  61 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 150 237 3 20 50 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 150 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 150 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 150 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 150 237 3 19 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 150 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 56
  150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 150 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 55 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 150 237 3 18 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 150 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 150 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 150 237 (Polychromatic418967fa.accept_9_7_6_3_1_456
  52 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 150 237 3 17 50 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 150 237
  (Polychromatic418967fa.accept_9_5_6_3_1_40 50 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 150 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 150 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 150 237 3 16 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 150 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 47
  150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 150 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 46 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 150 237 3 15 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 150 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 150 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 150 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 43
  150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 150 237 3 14 50 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 150 237
  (Polychromatic418967fa.accept_9_5_6_3_1_40 41 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 150 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 150 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 150 237 3 13 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 150 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 38
  150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 150 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 237 3 12 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 150 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 150 237 (Polychromatic418967fa.accept_9_7_6_3_1_456
  34 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 150 237 3 11 50 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 150 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 150 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 150 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 150 237 3 10 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 150 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 150 237 3 9 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 150 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 150 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 150 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 150 237 3 8 50 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 150 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 150 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 150 237 3 7 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 150 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 20
  150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 237 3 6 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 150 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 150 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 150 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 150 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 150 237 3 5 50 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 150 237
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 150 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 150 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 237 3 4 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 150 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 150 237 3 3 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 150 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 150 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 150 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 237 3 2 50 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 237
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 150 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 150 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 150 237 3 1 50 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 150 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 150 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 150 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 150 237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  89 149 237 (Eq.refl Bool.true) (allA_succ_of_accept 88 149 237 (accept_3_4 88 149 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 149 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 149 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 86
  149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 149 237 (accept_3_4 85
  149 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 149 237
  (Polychromatic418967fa.accept_15_9_14_12_1_913 84 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 149 237 (Polychromatic418967fa.accept_9_2_5_3_1_37 83 149 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 149 237 (accept_3_4 82 149 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 149 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 149 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 80
  149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 149 237 (accept_3_4 79
  149 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 149 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 78 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 149 237 (Polychromatic418967fa.accept_15_2_14_12_1_2453 77 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 149 237 (accept_3_4 76 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 149 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 75 149 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 149 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 74 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 149 237 (accept_3_4 73 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 149 237 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 149 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 149 237 (accept_3_4 70 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 149 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 149 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 149 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 149 237 (accept_3_4 67 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 149 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 149 237 (Polychromatic418967fa.accept_9_2_5_3_1_37 65 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 149 237 (accept_3_4 64 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 149 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 149 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 149 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 149 237 (accept_3_4 61 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 149 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 149 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 149 237 (accept_3_4 58 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 149 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 149 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 149 237 (accept_3_4 55 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 149 237 (Polychromatic418967fa.accept_15_9_14_12_1_913 54 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 149 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 237 (accept_3_4 52 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 149 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 149 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 149 237 (accept_3_4 49 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 149 237 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 149 237 (Polychromatic418967fa.accept_9_2_5_3_1_37 47 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 237 (accept_3_4 46 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 149 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 149 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 149 237 (accept_3_4 43 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 149 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 149 237 (Polychromatic418967fa.accept_15_11_14_12_1_2458 41 149 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 237 (accept_3_4 40 149 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 149 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 237 (accept_3_4 37 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 149 237 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 237 (accept_3_4 34 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 149 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 149 237 (accept_3_4 31 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 149 237 (Polychromatic418967fa.accept_20_10_9_17_1_12902 30 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 149 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 237 (accept_3_4 28 149 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 149
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 237 (accept_3_4 25 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 237 (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 149 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 237 (accept_3_4 22 149 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 237 (Polychromatic418967fa.accept_28_21_9_13_1_14181 21
  149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 237 (accept_3_4 19 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 237 (accept_3_4 16 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 149 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 237 (accept_3_4 13 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 237 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 237 (accept_3_4 10 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 237 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 149 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 237 (accept_3_4 7 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 237 (Polychromatic418967fa.accept_13_5_6_3_1_868 5 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 237 (accept_3_4 4 149 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 149 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 237 (accept_3_4 1 149 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 148 237
  (Eq.refl Bool.true) (allA_succ_of_accept 89 148 237 (accept_3_5 89 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 148 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 88 148 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 148 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 87 148 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 148 237 (accept_3_5 86 148 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 148 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 85
  148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 148 237
  (Polychromatic418967fa.accept_13_6_5_3_1_426 84 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 148 237 (accept_3_5 83 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 148 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 148 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 81 148 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 148 237 (accept_3_5 80 148 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 148 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 148 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 78 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 148 237 (accept_3_5 77 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 148 237 (Polychromatic418967fa.accept_11_10_5_6_1_1842 76 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 148 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 148 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 148 237 (accept_3_5 74 148 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 148 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 148 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 148 237 (accept_3_5 71 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 148 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 148 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 69 148 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 148 237 (accept_3_5 68 148 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 148 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 148 237
  (Polychromatic418967fa.accept_12_6_4_9_1_544 66 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 148 237 (accept_3_5 65 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 148 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 64 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 148 237 (Polychromatic418967fa.accept_13_11_5_3_1_889 63 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 148 237 (accept_3_5 62 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 148 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 148 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 148 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 60 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 148 237 (accept_3_5 59 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 148 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 148 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 148 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 148 237 (accept_3_5 56 148 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 148 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 148 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 148 237 (accept_3_5 53 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 148 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 148 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 148 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 148 237 (accept_3_5 50 148 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 148 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 148 237
  (Polychromatic418967fa.accept_13_9_5_3_1_428 48 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 148 237 (accept_3_5 47 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 148 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 148 237 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 148 237 (accept_3_5 44 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 148 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 148 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 148 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 148 237 (accept_3_5 41 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 148 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 148 237 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 148 237 (accept_3_5 38 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 148 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 148 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 148 237
  (Polychromatic418967fa.accept_21_15_1_6_1_8258 36 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 148 237 (accept_3_5 35 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 148 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 148 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 148 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 148 237 (accept_3_5 32 148 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 148 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 148 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 148 237 (accept_3_5 29 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 148 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 148 237 (Polychromatic418967fa.accept_13_1_5_3_1_888 27 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 148 237 (accept_3_5 26 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 148 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 148 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 148 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 148 237 (accept_3_5 23 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 148 237 (Polychromatic418967fa.accept_13_9_5_3_1_428 22 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 148 237 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 148 237 (accept_3_5 20 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 148 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 148 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 148 237
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 148 237 (accept_3_5 17 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 148 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 148 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 148 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 148 237 (accept_3_5 14 148 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 148 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 148 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 148 237 (accept_3_5 11 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 148 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 148 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 148 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 148 237 (accept_3_5 8 148 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 148 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 148 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 148 237 (accept_3_5 5 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  148 237 (Polychromatic418967fa.accept_19_4_15_9_1_8845 4 148 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 148 237 (Polychromatic418967fa.accept_15_3_13_12_1_348 3 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 237 (accept_3_5 2 148 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 148 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 148 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 147 237
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 147 237 3 30 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 147 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 89 147 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 147 237
  (Polychromatic418967fa.accept_16_8_3_13_1_7295 88 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 147 237 3 29 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 147 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 147 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 147 237 (Polychromatic418967fa.accept_12_1_3_9_1_174
  85 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 147 237 3 28 49 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 147 237
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 83 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 147 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 147 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 147 237 3 27 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 147 237
  (Polychromatic418967fa.accept_17_12_11_16_1_6903 80 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 147 237 (Polychromatic418967fa.accept_11_2_4_6_1_2412 79 147 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 147 237 3 26 49 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 147 237
  (Polychromatic418967fa.accept_12_5_3_9_1_541 77 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 147 237 (Polychromatic418967fa.accept_14_6_7_13_1_3158 76 147 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 147 237 3 25 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 147 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 74
  147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 237
  (Polychromatic418967fa.accept_12_1_3_9_1_174 73 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 147 237 3 24 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 147 237 (Polychromatic418967fa.accept_12_11_3_9_1_1630 71 147 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 147 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 70 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 147 237 3 23 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 147 237 (Polychromatic418967fa.accept_11_2_4_6_1_2412 68 147 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 237
  (Polychromatic418967fa.accept_12_7_3_9_1_999 67 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 147 237 3 22 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 147 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 65 147 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 237
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 64 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 147 237 3 21 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 147 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 147 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 237 (Polychromatic418967fa.accept_12_1_3_9_1_174
  61 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 147 237 3 20 49 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 147 237
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 59 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 147 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 147 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 147 237 3 19 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 147 237 (Polychromatic418967fa.accept_16_8_3_13_1_7295
  56 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 237
  (Polychromatic418967fa.accept_12_7_3_9_1_999 55 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 147 237 3 18 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 147 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 53 147 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 237
  (Polychromatic418967fa.accept_20_12_7_17_1_12857 52 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 147 237 3 17 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 147 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 147 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 237
  (Polychromatic418967fa.accept_12_1_3_9_1_174 49 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 147 237 3 16 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 147 237 (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 147 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 147 237 3 15 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 147 237 (Polychromatic418967fa.accept_19_6_14_9_1_8863 44 147 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 237
  (Polychromatic418967fa.accept_12_7_3_9_1_999 43 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 147 237 3 14 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 147 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 147 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 237 (Polychromatic418967fa.accept_13_1_4_3_1_1545
  40 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 147 237 3 13 49 79
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 147 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 147 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 147 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 147 237 3 12 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 147 237 (Polychromatic418967fa.accept_11_2_4_6_1_2412
  35 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 147 237 3 11 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 147 237 (Polychromatic418967fa.accept_17_15_11_16_1_3263 32 147 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 237
  (Polychromatic418967fa.accept_12_7_3_9_1_999 31 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 147 237 3 10 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 147 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 147 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 237
  (Polychromatic418967fa.accept_20_8_7_17_1_8576 28 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 147 237 3 9 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 147 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 147 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 147
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 147 237 3 8 49 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 147 237
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 147 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 147 237 3 7 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 147 237 (Polychromatic418967fa.accept_13_7_4_3_1_3064
  20 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 237
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 147 237 3 6 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 147 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 147 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 237 (Polychromatic418967fa.accept_19_16_14_9_1_7316 16 147
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 147 237 3 5 49 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 147 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 147 237 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 147 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 147 237 3 4 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 147 237 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  11 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 147 237 3 3 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 147 237 (Polychromatic418967fa.accept_14_8_7_13_1_4113 8 147 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 237 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 147 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 147 237 3 2 49 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 237
  (Polychromatic418967fa.accept_12_5_3_9_1_541 5 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 237 (Polychromatic418967fa.accept_19_4_14_9_1_10227 4 147 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 147 237 3 1 49 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 147 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 147 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 237
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 147 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 147 237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 92 146 237 (Eq.refl Bool.true) (allA_succ_of_accept 91 146 237 (accept_3_4 91 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 146 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 90 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 146 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 89 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 146 237 (accept_3_4 88 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 146 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 146 237 (Polychromatic418967fa.accept_9_5_2_3_1_194 86 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 146 237 (accept_3_4 85 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 146 237 (Polychromatic418967fa.accept_18_12_2_3_1_6414 84 146 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 146 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 83 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 146 237 (accept_3_4 82 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 146 237 (Polychromatic418967fa.accept_10_1_6_7_1_710 81 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 146 237 (Polychromatic418967fa.accept_9_8_2_3_1_447 80 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 146 237 (accept_3_4 79 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 146 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 78 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 146 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 146 237 (accept_3_4 76 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 146 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 146 237 (Polychromatic418967fa.accept_11_8_3_6_1_1855 74 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 146 237 (accept_3_4 73 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 146 237 (Polychromatic418967fa.accept_19_15_13_9_1_7324 72 146
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 146 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 146 237 (accept_3_4 70 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 146 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 146 237 (Polychromatic418967fa.accept_9_5_2_3_1_194 68 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 146 237 (accept_3_4 67 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 146 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 66 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 146 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 146 237 (accept_3_4 64 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 146 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 146 237 (Polychromatic418967fa.accept_9_8_2_3_1_447 62 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 146 237 (accept_3_4 61 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 146 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 146 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 146 237 (accept_3_4 58 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 146 237 (Polychromatic418967fa.accept_17_6_10_16_1_9453 57 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 146 237 (Polychromatic418967fa.accept_19_18_13_9_1_5971 56 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 146 237 (accept_3_4 55 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 146 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 54 146
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 146 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 146 237 (accept_3_4 52 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 146 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 146 237 (Polychromatic418967fa.accept_9_5_2_3_1_194 50 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 146 237 (accept_3_4 49 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 146 237 (Polychromatic418967fa.accept_18_12_2_3_1_6414 48 146 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 146 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 146 237 (accept_3_4 46 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 146 237 (Polychromatic418967fa.accept_18_9_2_3_1_5082 45 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 146 237 (Polychromatic418967fa.accept_9_8_2_3_1_447 44 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 146 237 (accept_3_4 43 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 146 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 146 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 146 237 (accept_3_4 40 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 146 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 146 237 (Polychromatic418967fa.accept_15_8_11_12_1_1626 38 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 146 237 (accept_3_4 37 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 146 237 (Polychromatic418967fa.accept_19_17_13_9_1_5970 36 146
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 146 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 146 237 (accept_3_4 34 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 146 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 146 237 (Polychromatic418967fa.accept_9_5_2_3_1_194 32 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 146 237 (accept_3_4 31 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 146 237 (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 146 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 146 237 (accept_3_4 28 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 146 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 146 237 (Polychromatic418967fa.accept_9_8_2_3_1_447 26 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 146 237 (accept_3_4 25 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 146 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 146 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 146 237 (accept_3_4 22 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 146 237 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 146 237 (Polychromatic418967fa.accept_11_9_3_6_1_797 20 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 146 237 (accept_3_4 19 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 146 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 146
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 146 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 146 237 (accept_3_4 16 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 146 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 146 237 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 146 237 (accept_3_4 13 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 146 237 (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 146 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 146 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 146 237 (accept_3_4 10 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  146 237 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 146 237 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 146 237 (accept_3_4 7 146 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 146 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 146 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 146 237 (accept_3_4 4 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  146 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 146 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 146 237 (Polychromatic418967fa.accept_21_2_20_6_1_2277 2 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 146 237 (accept_3_4 1 146 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 146
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 145 237
  (Eq.refl Bool.true) (allA_succ_of_accept 92 145 237 (accept_3_5 92 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 145 237 (Polychromatic418967fa.accept_17_6_9_16_1_4410 91 145 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 145 237 (Polychromatic418967fa.accept_13_12_2_3_1_1527 90 145
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 145 237 (accept_3_5 89 145
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 145 237
  (Polychromatic418967fa.accept_6_4_1_3_1_77 88 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 145 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 87 145 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 145 237 (accept_3_5 86 145 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 145 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 85 145 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 145 237 (Polychromatic418967fa.accept_8_4_1_5_1_186
  84 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 145 237 (accept_3_5 83
  145 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 145 237
  (Polychromatic418967fa.accept_6_4_1_3_1_77 82 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 145 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 145 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 145 237 (accept_3_5 80 145 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 145 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 79 145 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 145 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 78
  145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 145 237 (accept_3_5 77
  145 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 145 237
  (Polychromatic418967fa.accept_6_4_1_3_1_77 76 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 145 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 75 145 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 145 237 (accept_3_5 74 145 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 145 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 73 145 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 145 237
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 145 237 (accept_3_5 71 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 145 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 145 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 69 145 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 145 237 (accept_3_5 68 145 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 145 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 67 145 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 145 237
  (Polychromatic418967fa.accept_13_1_2_3_1_911 66 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 145 237 (accept_3_5 65 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 145 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 145 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 145 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 145 237 (accept_3_5 62 145 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 145 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 61 145 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 145 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 145 237 (accept_3_5 59 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 145 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 145 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 145 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 145 237 (accept_3_5 56 145 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 145 237 (Polychromatic418967fa.accept_20_15_5_17_1_5495 55 145 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 145 237
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 54 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 145 237 (accept_3_5 53 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 145 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 145 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 145 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 145 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 145 237 (accept_3_5 50 145 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 145 237 (Polychromatic418967fa.accept_9_4_1_3_1_190
  49 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 145 237
  (Polychromatic418967fa.accept_10_8_5_7_1_358 48 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 145 237 (accept_3_5 47 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 145 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 145 237 (Polychromatic418967fa.accept_18_9_1_3_1_6451 45 145 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 145 237 (accept_3_5 44 145 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 145 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 145 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 145 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 145 237 (accept_3_5 41 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 145 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 145 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 145 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 145 237 (accept_3_5 38 145 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 145 237 (Polychromatic418967fa.accept_11_4_2_6_1_389 37 145 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 145 237 (accept_3_5 35 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 145 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 145 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 145 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 237 (accept_3_5 32 145 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 145 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 145 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 145 237
  (Polychromatic418967fa.accept_16_14_1_13_1_2754 30 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 145 237 (accept_3_5 29 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 145 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 145 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 145
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 237 (accept_3_5 26 145
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 145 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 145 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 145 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 237 (accept_3_5 23 145 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 145 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 145 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 237
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 21 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 145 237 (accept_3_5 20 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 145 237 (Polychromatic418967fa.accept_16_3_1_13_1_4968 19 145 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 145 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 237 (accept_3_5 17 145 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 237 (accept_3_5 14 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 145 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 237 (accept_3_5 11 145 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 145 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 237
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 237 (accept_3_5 8 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 145 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 237 (accept_3_5 5 145 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 145 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 237
  (Polychromatic418967fa.accept_10_3_5_7_1_330 3 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 237 (accept_3_5 2 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 145 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_237_segment_001))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


