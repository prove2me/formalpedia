-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch260
-- name    : Polychromatic418967fa_Branch260
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:30:22.832226+00:00
-- url     : https://prove2.me/theorems/09321b7c-43ce-482d-b91f-00f8fefe5b47
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch260_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_260 : allB 260 260 :=
  allB_succ' 2 259 260 (Eq.refl Bool.true) (allA_of_3_0 2 259 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  258 260 (Eq.refl Bool.true) (allA_succ_of_gcd 2 258 260 2 1 129 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 258 260 (accept_3_2 1 258 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 258 260))) (allB_succ' 4 257 260 (Eq.refl Bool.true) (allA_succ_of_accept 3 257 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 257 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 257 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 257 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 257 260 (accept_3_2 1 257 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 257 260)))) (allB_succ' 5 256 260 (Eq.refl Bool.true) (allA_of_3_0 5 256 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 255 260 (Eq.refl Bool.true) (allA_succ_of_gcd 5 255 260 5 1 51 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 255 260 (accept_3_2 4
  255 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 255 260
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 255 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 255 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 255 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 255 260 (accept_3_2 1 255 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 255 260)))))) (allB_succ' 7 254 260 (Eq.refl Bool.true) (allA_succ_of_gcd 6 254 260 2 3 127 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 254 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 254 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 254 260 2 2 127 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 254 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 254 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 254 260 2 1 127 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 254 260 (accept_3_2 1 254 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 254 260))))))) (allB_succ' 8 253 260 (Eq.refl Bool.true) (allA_of_3_0 8 253
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 252 260 (Eq.refl Bool.true) (allA_succ_of_gcd 8 252 260 4 2
  63 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 252 260
  (accept_3_2 7 252 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 252 260 2 3 126 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 252 260
  (Polychromatic418967fa.accept_16_5_12_4_1_4325 5 252 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 252 260 4 1 63 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 252 260 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 252 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 252 260 2 1 126 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 252 260 (accept_3_2 1 252 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 252 260))))))))) (allB_succ' 10 251 260 (Eq.refl Bool.true) (allA_succ_of_accept 9 251
  260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 251 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 251 260 (Polychromatic418967fa.accept_15_8_11_5_1_169 8 251 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 251 260 (accept_3_2 7 251 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 251 260 (Polychromatic418967fa.accept_15_6_11_5_1_168 6 251 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 251 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 5
  251 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 251 260 (accept_3_2 4 251
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 251 260 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 251 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 251 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 251 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 251 260 (accept_3_2 1 251 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 251
  260)))))))))) (allB_succ' 11 250 260 (Eq.refl Bool.true) (allA_of_3_0 11 250 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 249 260 (Eq.refl Bool.true) (allA_succ_of_accept 11 249 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 249 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 249 260 (accept_3_2 10 249 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  249 260 (Polychromatic418967fa.accept_21_9_18_8_1_11475 9 249 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 249 260 (Polychromatic418967fa.accept_16_8_9_4_1_630 8 249 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 249 260 (accept_3_2 7 249 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 249 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 249 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 249 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 249 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 249 260 (accept_3_2 4 249 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  249 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 249 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 249 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 249 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 249 260 (accept_3_2 1 249 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 249 260)))))))))))) (allB_succ' 13 248 260 (Eq.refl Bool.true) (allA_succ_of_gcd 12 248
  260 4 3 62 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  248 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 248 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 248 260 2 5 124 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 248 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 248 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 248 260 4 2 62 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 248 260 (accept_3_2 7 248 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 248 260 2 3 124 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 248 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 5
  248 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 248 260 4 1 62 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 248 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 248 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 248 260 2 1 124 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 248 260 (accept_3_2 1 248 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 248
  260))))))))))))) (allB_succ' 14 247 260 (Eq.refl Bool.true) (allA_of_3_0 14 247 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 246 260 (Eq.refl Bool.true) (allA_succ_of_gcd 14 246 260 2 7 123 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 246 260 (accept_3_2 13 246 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 246 260 2 6 123 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 246 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 246 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 246 260 2 5 123 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 246 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 246 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 246 260 2 4 123 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 246 260 (accept_3_2 7 246 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 246 260 2 3 123 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 246 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 5
  246 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 246 260 2 2 123 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 246 260
  (Polychromatic418967fa.accept_11_3_4_7_1_114 3 246 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 246 260 2 1 123 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 246 260 (accept_3_2 1 246 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 246
  260))))))))))))))) (allB_succ' 16 245 260 (Eq.refl Bool.true) (allA_succ_of_gcd 15 245 260 5 3 49 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 245 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 245 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 245 260 (accept_3_2 13 245 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 245 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 245 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 245 260 (Polychromatic418967fa.accept_17_11_7_5_1_1567 11 245 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 245 260 5 2 49 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 245 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 245 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 245 260 (Polychromatic418967fa.accept_16_8_5_4_1_674 8 245 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 245 260 (accept_3_2 7 245 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 245 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 245 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 245 260 5 1 49 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 245 260 (accept_3_2 4 245 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 245 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 245 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 245 260
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 245 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 245 260 (accept_3_2 1 245 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 245
  260)))))))))))))))) (allB_succ' 17 244 260 (Eq.refl Bool.true) (allA_of_3_0 17 244 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 243 260 (Eq.refl Bool.true) (allA_succ_of_accept 17 243 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 243 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 243 260 (accept_3_2 16 243 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 243 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 243 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 243 260 (Polychromatic418967fa.accept_19_14_15_13_1_4898 14 243 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 243 260 (accept_3_2 13 243 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 243 260 (Polychromatic418967fa.accept_16_12_3_4_1_4317 12 243
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 243 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 243 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 243 260 (accept_3_2 10 243 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  243 260 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 243 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 243 260 (Polychromatic418967fa.accept_15_8_3_5_1_608 8 243 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 243 260 (accept_3_2 7 243 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 243 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 243 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 243 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 243 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 243 260 (accept_3_2 4 243 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  243 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 243 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 243 260 (Polychromatic418967fa.accept_15_2_3_5_1_2991 2 243 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 243 260 (accept_3_2 1 243 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 243 260)))))))))))))))))) (allB_succ' 19 242 260 (Eq.refl Bool.true) (allA_succ_of_gcd
  18 242 260 2 9 121 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 242 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 242 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 242 260 2 8 121 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 242 260
  (Polychromatic418967fa.accept_19_15_14_13_1_2343 15 242 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 242 260 2 7 121 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 242 260 (accept_3_2 13 242 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 242 260 2 6 121 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 242 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 242 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 242 260 2 5 121 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 242 260
  (Polychromatic418967fa.accept_27_9_26_17_1_980 9 242 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 242 260 2 4 121 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 242 260 (accept_3_2 7 242 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 242 260 2 3 121 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 242 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 242 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 242 260 2 2 121 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 242 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 242 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 242 260 2 1 121 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 242 260 (accept_3_2 1 242 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 242
  260))))))))))))))))))) (allB_succ' 20 241 260 (Eq.refl Bool.true) (allA_of_3_0 20 241 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 240 260 (Eq.refl Bool.true) (allA_succ_of_gcd 20 240 260 20 1 12 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 240 260 (accept_3_2 19 240 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 240 260 2 9 120 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 240 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 240 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 240 260 4 4 60 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 240 260 5 3 48 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 240 260 2 7 120 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 240 260 (accept_3_2 13 240 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 240 260 4 3 60 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 240 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 240 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 240 260 10 1 24 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 240 260 (Polychromatic418967fa.accept_18_9_6_8_1_2989 9
  240 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 240 260 4 2 60 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 240 260 (accept_3_2 7
  240 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 240 260 2 3 120 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 240 260 5 1 48 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 240 260 4 1 60 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 240 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 240 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 240 260 2 1 120 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 240 260 (accept_3_2 1 240 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240
  260))))))))))))))))))))) (allB_succ' 22 239 260 (Eq.refl Bool.true) (allA_succ_of_accept 21 239 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 239 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 239 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 239 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 239 260 (accept_3_2 19 239 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 239 260 (Polychromatic418967fa.accept_25_18_14_10_1_15894 18 239 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 239 260
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 239 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 239 260 (accept_3_2 16 239 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 239 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 239 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 239 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 239 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 239 260 (accept_3_2 13 239 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 239 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 239 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 239 260
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 239 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 239 260 (accept_3_2 10 239 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  239 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 239 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 239 260 (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 239 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 239 260 (accept_3_2 7 239 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 239 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 239 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 239 260
  (Polychromatic418967fa.accept_16_5_15_4_1_9099 5 239 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 239 260 (accept_3_2 4 239 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  239 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 239 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 239 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 239 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 239 260 (accept_3_2 1 239 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 239 260)))))))))))))))))))))) (allB_succ' 23 238 260 (Eq.refl Bool.true) (allA_of_3_0
  23 238 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 237 260 (Eq.refl Bool.true) (allA_succ_of_accept 23
  237 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 237 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 237 260 (accept_3_2 22 237 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 237 260 (Polychromatic418967fa.accept_14_7_13_8_1_2067 21 237 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 237 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 237 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 237 260 (accept_3_2 19 237 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 237 260 (Polychromatic418967fa.accept_12_6_9_8_1_165
  18 237 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 237 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 237 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 237 260 (accept_3_2 16 237 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 237 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 237 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 237 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 237 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 237 260 (accept_3_2 13 237 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 237 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 237 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 237 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 237 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 237 260 (accept_3_2 10 237 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  237 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 237 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 237 260 (Polychromatic418967fa.accept_15_8_12_5_1_2987 8 237 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 237 260 (accept_3_2 7 237 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 237 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 237 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 237 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 237 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 237 260 (accept_3_2 4 237 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  237 260 (Polychromatic418967fa.accept_19_3_9_13_1_15893 3 237 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 237 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 237 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 260 (accept_3_2 1 237 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 237 260)))))))))))))))))))))))) (allB_succ' 25 236 260 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 236 260 4 6 59 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 236 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 236 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 236 260 2 11 118 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 236 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 21
  236 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 236 260 4 5 59 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 236 260 (accept_3_2 19
  236 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 236 260 2 9 118 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 236 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 236 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 236 260 4 4 59 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 236 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 236 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 236 260 2 7 118 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 236 260 (accept_3_2 13 236 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 236 260 4 3 59 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 236 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 236 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 236 260 2 5 118 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 236 260
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 236 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 236 260 4 2 59 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 236 260 (accept_3_2 7 236 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 236
  260 2 3 118 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  236 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 236 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 236 260 4 1 59 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 236 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 236 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 236 260 2 1 118 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 236 260 (accept_3_2 1 236 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 236 260))))))))))))))))))))))))) (allB_succ' 26 235 260 (Eq.refl Bool.true)
  (allA_of_3_0 26 235 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 234 260 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 234 260 26 1 9 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 234 260 (accept_3_2 25 234 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24
  234 260 2 12 117 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 234 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 234 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 234 260 2 11 117 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 234 260 (Polychromatic418967fa.accept_11_10_3_7_1_2564
  21 234 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 234 260 2 10 117 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 234 260
  (accept_3_2 19 234 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 234 260 2 9 117 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 234 260
  (Polychromatic418967fa.accept_19_17_6_13_1_6334 17 234 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 234 260 2 8 117 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 234 260 (Polychromatic418967fa.accept_11_4_3_7_1_828 15 234 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 234 260 2 7 117 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 13 234 260 13 1 18 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 234 260 2 6 117 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 234 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 234 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 234 260 2 5 117 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 234 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 234 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 234 260 2 4 117 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 234 260 (accept_3_2 7 234 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 234 260 2 3 117 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 234 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 5
  234 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 234 260 2 2 117 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 234 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 234 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 234 260 2 1 117 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 234 260 (accept_3_2 1 234 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 234
  260))))))))))))))))))))))))))) (allB_succ' 28 233 260 (Eq.refl Bool.true) (allA_succ_of_accept 27 233 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 233 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 233 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 233 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 233 260 (accept_3_2 25 233 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 233 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 233 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 233 260
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 23 233 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 233 260 (accept_3_2 22 233 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 233 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 233 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 233 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 233 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 233 260 (accept_3_2 19 233 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 233 260 (Polychromatic418967fa.accept_15_3_8_5_1_2105 18 233 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 233 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 233 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 233 260 (accept_3_2 16 233 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 233 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 233 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 233 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 233 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 233 260 (accept_3_2 13 233 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 233 260 (Polychromatic418967fa.accept_15_12_8_5_1_5048 12 233
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 233 260
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 233 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 233 260 (accept_3_2 10 233 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  233 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 233 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 233 260 (Polychromatic418967fa.accept_16_8_9_4_1_630 8 233 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 233 260 (accept_3_2 7 233 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 233 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 233 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 233 260
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 233 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 233 260 (accept_3_2 4 233 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  233 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 233 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 233 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 233 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 233 260 (accept_3_2 1 233 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 233 260)))))))))))))))))))))))))))) (allB_succ' 29 232 260 (Eq.refl Bool.true)
  (allA_of_3_0 29 232 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 231 260 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 231 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 231 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 231 260 (accept_3_2 28 231 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 231 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 231 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 231 260
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 231 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 231 260 (accept_3_2 25 231 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 231 260 (Polychromatic418967fa.accept_16_8_7_4_1_2217 24 231 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 231 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 231 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 231 260 (accept_3_2 22 231 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 231 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 231 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 231 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 231 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 231 260 (accept_3_2 19 231 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 231 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 231 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 231 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 231 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 260 (accept_3_2 16 231 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 231 260 (Polychromatic418967fa.accept_14_1_7_8_1_2063 15 231 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 231 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 231 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 231 260 (accept_3_2 13 231 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 231 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 231 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 231 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 231 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 260 (accept_3_2 10 231 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 231 260 (Polychromatic418967fa.accept_19_9_3_13_1_2300 9 231 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 260
  (Polychromatic418967fa.accept_16_8_7_4_1_2217 8 231 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 231 260 (accept_3_2 7 231 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  231 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 231 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 231 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 231 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 260 (accept_3_2 4 231 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 231 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 231 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 231 260 (accept_3_2 1 231 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231
  260)))))))))))))))))))))))))))))) (allB_succ' 31 230 260 (Eq.refl Bool.true) (allA_succ_of_gcd 30 230 260 10 3 23 26
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 230 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 230 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 230 260 2 14 115 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 230 260 (Polychromatic418967fa.accept_16_11_6_4_1_2228 27 230 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 230 260 2 13 115 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 230 260 5 5 46 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 230 260 2 12 115 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 230 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 230 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 230 260 2 11 115 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 230 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 230 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 230 260 10 2 23 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 230 260 (accept_3_2 19 230 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 230 260 2 9 115 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 230 260 (Polychromatic418967fa.accept_12_5_2_8_1_172
  17 230 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 230 260 2 8 115 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 230 260 5 3 46 52
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 230 260 2 7 115
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 230 260
  (accept_3_2 13 230 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 230 260 2 6 115 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 230 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 230 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 230 260 10 1 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 230 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 230 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 230 260 2 4 115 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 230 260 (accept_3_2 7 230 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 230 260 2 3 115 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 230 260 5 1 46 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 230 260 2 2 115 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 230 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 230 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 230 260 2 1 115 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 230 260 (accept_3_2 1 230 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230
  260))))))))))))))))))))))))))))))) (allB_succ' 32 229 260 (Eq.refl Bool.true) (allA_of_3_0 32 229 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 228 260 (Eq.refl Bool.true) (allA_succ_of_gcd 32 228 260 4 8 57 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 228 260
  (accept_3_2 31 228 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 228 260 2 15 114 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 228 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 228 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 228 260 4 7 57 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 228 260 (Polychromatic418967fa.accept_28_27_4_8_1_9952 27 228 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 228 260 2 13 114 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 228 260 (accept_3_2 25 228 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 228 260 4 6 57 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 228 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 228 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 228 260 2 11 114 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 228 260
  (Polychromatic418967fa.accept_15_6_3_5_1_607 21 228 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 228 260 4 5 57 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 228 260 (accept_3_2 19 228 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  228 260 2 9 114 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 228 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 228 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 228 260 4 4 57 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 228 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 15
  228 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 228 260 2 7 114 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 228 260 (accept_3_2 13
  228 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 228 260 4 3 57 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 228 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 228 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 228 260 2 5 114 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 228 260 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 228 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 228 260 4 2 57 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 228 260 (accept_3_2 7 228 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 228 260 2 3 114 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 228 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 228 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 228 260 4 1 57 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 228 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 228 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 228 260 2 1 114 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 228 260 (accept_3_2 1 228 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228
  260))))))))))))))))))))))))))))))))) (allB_succ' 34 227 260 (Eq.refl Bool.true) (allA_succ_of_accept 33 227 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 227 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 227 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 227 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 227 260 (accept_3_2 31 227 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 227 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 227 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 227 260
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 227 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 227 260 (accept_3_2 28 227 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 227 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 227 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 227 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 227 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 227 260 (accept_3_2 25 227 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 227 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 227 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 227 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 227 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 227 260 (accept_3_2 22 227 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 227 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 227 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 227 260 (Polychromatic418967fa.accept_17_3_6_5_1_8669 20 227 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 227 260 (accept_3_2 19 227 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 227 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 227 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 227 260
  (Polychromatic418967fa.accept_16_1_3_4_1_665 17 227 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 227 260 (accept_3_2 16 227 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 227 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 227 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 227 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 227 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 227 260 (accept_3_2 13 227 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 227 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 227 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 227 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 227 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 227 260 (accept_3_2 10 227 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  227 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 227 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 227 260 (Polychromatic418967fa.accept_16_8_3_4_1_3233 8 227 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 260 (accept_3_2 7 227 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 227 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 227 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 227 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 227 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 227 260 (accept_3_2 4 227 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  227 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 227 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 227 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 227 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 260 (accept_3_2 1 227 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 227 260)))))))))))))))))))))))))))))))))) (allB_succ' 35 226 260 (Eq.refl Bool.true)
  (allA_of_3_0 35 226 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 225 260 (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 225 260 5 7 45 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 225 260 (accept_3_2 34 225 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 225 260 (Polychromatic418967fa.accept_17_16_4_5_1_3626 33 225 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 225 260 (Polychromatic418967fa.accept_24_8_9_20_1_7244 32 225 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 225 260 (accept_3_2 31 225 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 225 260 5 6 45 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 225 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29
  225 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 225 260 (accept_3_2 28
  225 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 225 260
  (Polychromatic418967fa.accept_21_6_15_8_1_9895 27 225 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 225 260 (Polychromatic418967fa.accept_21_5_15_8_1_9935 26 225 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 225 260 5 5 45 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 225 260 (Polychromatic418967fa.accept_16_8_1_4_1_6622
  24 225 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 225 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 225 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 225 260 (accept_3_2 22 225 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 225 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 225 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 225 260 5 4 45 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 225 260 (accept_3_2 19 225 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 225 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 225 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 225 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 225 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 260 (accept_3_2 16 225 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 225 260 5 3 45 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 225 260
  (Polychromatic418967fa.accept_16_14_1_4_1_5432 14 225 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 225 260 (accept_3_2 13 225 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 225 260 (Polychromatic418967fa.accept_16_12_1_4_1_5403 12 225 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 225 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 225 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 225 260 5 2 45 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 225 260
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 225 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 225 260 (Polychromatic418967fa.accept_16_8_1_4_1_6622 8 225 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 260 (accept_3_2 7 225 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 225 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 225 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 225 260 5 1 45 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 225 260 (accept_3_2 4 225 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 260 (Polychromatic418967fa.accept_16_3_1_4_1_5426 3 225 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 260
  (Polychromatic418967fa.accept_14_2_1_8_1_650 2 225 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 225 260 (accept_3_2 1 225 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225
  260)))))))))))))))))))))))))))))))))))) (allB_succ' 37 224 260 (Eq.refl Bool.true) (allA_succ_of_gcd 36 224 260 4 9 56
  65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 224 260
  (Polychromatic418967fa.accept_19_16_15_13_1_1335 35 224 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 224 260 2 17 112 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 224 260 (Polychromatic418967fa.accept_19_14_15_13_1_4898 33 224 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 224 260 4 8 56 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 224 260 (accept_3_2 31
  224 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 224 260 2 15 112 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 224 260
  (Polychromatic418967fa.accept_23_6_17_7_1_9295 29 224 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 224 260 4 7 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 224 260 (Polychromatic418967fa.accept_21_6_14_8_1_9908 27 224 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 224 260 2 13 112 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 224 260 (accept_3_2 25 224 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 224 260 4 6 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 224 260 (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 224
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 224 260 2 11 112 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 224 260
  (Polychromatic418967fa.accept_15_6_14_5_1_2976 21 224 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 224 260 4 5 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 224 260 (accept_3_2 19 224 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  224 260 2 9 112 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 224 260 (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 224 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 224 260 4 4 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 224 260
  (Polychromatic418967fa.accept_21_15_14_8_1_6826 15 224 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 224 260 2 7 112 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 224 260 (accept_3_2 13 224 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 224 260 4 3 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 224 260 (Polychromatic418967fa.accept_21_11_14_8_1_5256 11 224 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 224 260 2 5 112 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 224 260
  (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 224 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 224 260 4 2 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 224 260 (accept_3_2 7 224 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 224
  260 2 3 112 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  224 260 (Polychromatic418967fa.accept_21_5_14_8_1_6818 5 224 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 224 260 4 1 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 224 260 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 224 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 224 260 2 1 112 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 224 260 (accept_3_2 1 224 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 224 260))))))))))))))))))))))))))))))))))))) (allB_succ' 38 223 260 (Eq.refl
  Bool.true) (allA_of_3_0 38 223 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 222 260 (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 222 260 2 19 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 222 260 (accept_3_2 37 222 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 222 260 2 18 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 222 260 (Polychromatic418967fa.accept_21_14_12_8_1_6833 35 222 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 222 260 2 17 111 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 222 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 222 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 222 260 2 16 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 222 260 (accept_3_2 31 222 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 222 260 2 15 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 222 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 222 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 222 260 2 14 111 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 222 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 222 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 222 260 2 13 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 222 260 (accept_3_2 25 222 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 222 260 2 12 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 222 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 222 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 222 260 2 11 111 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 222 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 222 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 222 260 2 10 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 222 260 (accept_3_2 19 222 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 222 260 2 9 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 222 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 222 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 222 260 2 8 111 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 222 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 222 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 222 260 2 7 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 222 260 (accept_3_2 13 222 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 222 260 2 6 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 222 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 222 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 222 260 2 5 111 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 222 260
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 222 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 222 260 2 4 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 222 260 (accept_3_2 7 222 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 260 2 3 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 222 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 222 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 222 260 2 2 111 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 222 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 222 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 222 260 2 1 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 222 260 (accept_3_2 1 222 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222
  260))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 221 260 (Eq.refl Bool.true) (allA_succ_of_gcd 39 221 260 13
  3 17 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 221
  260 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 221 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 221 260 (accept_3_2 37 221 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 221 260 (Polychromatic418967fa.accept_15_6_11_5_1_168 36 221 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 221 260 (Polychromatic418967fa.accept_18_17_5_8_1_1898 35 221 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 221 260 (accept_3_2 34 221 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 221 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 221 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 221 260
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 32 221 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 221 260 (accept_3_2 31 221 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 221 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 221 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 221 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 221 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 221 260 (accept_3_2 28 221 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 221 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 221 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 221 260 13 2 17 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 221 260 (accept_3_2 25 221 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 221 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 24
  221 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 221 260
  (Polychromatic418967fa.accept_15_8_11_5_1_169 23 221 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 221 260 (accept_3_2 22 221 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 221 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 221 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 221 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 221 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 221 260 (accept_3_2 19 221 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 221 260 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 221 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 221 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 221 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 221 260 (accept_3_2 16 221 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 221 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 221 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 221 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 221 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 221 260 13 1 17 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 221 260
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 221 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 221 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 221 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 221 260 (accept_3_2 10 221 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 221 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 221 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 260 (Polychromatic418967fa.accept_15_8_11_5_1_169
  8 221 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 221 260 (accept_3_2 7
  221 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 221 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 6 221 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 221 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 221 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 260 (accept_3_2 4 221 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 221 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 221 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 2
  221 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 221 260 (accept_3_2 1 221
  260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221 260)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41
  220 260 (Eq.refl Bool.true) (allA_of_3_0 41 220 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 219 260
  (Eq.refl Bool.true) (allA_succ_of_accept 41 219 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 219 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 219 260 (accept_3_2 40 219 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 219 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 219 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 219 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 219 260 (accept_3_2 37 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 219 260 (Polychromatic418967fa.accept_11_3_10_7_1_129 36 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 219 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 219 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 219 260 (accept_3_2 34 219 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 219 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 219 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 219 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 219 260 (accept_3_2 31 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 219 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 219 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 219 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 219 260 (accept_3_2 28 219 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 219 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 219 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 219 260
  (Polychromatic418967fa.accept_15_11_9_5_1_2974 26 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 219 260 (accept_3_2 25 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 219 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 219 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 219 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 219 260 (accept_3_2 22 219 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 219 260 (Polychromatic418967fa.accept_19_2_10_13_1_9147 21 219 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 260
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 219 260 (accept_3_2 19 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 219 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 219 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 219 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 260 (accept_3_2 16 219 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 219 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 219 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 219 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 219 260 (accept_3_2 13 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 219 260 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 219 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 219 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 260 (accept_3_2 10 219 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 260 (Polychromatic418967fa.accept_16_9_11_4_1_3194 9 219 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 260
  (Polychromatic418967fa.accept_16_8_11_4_1_3290 8 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 219 260 (accept_3_2 7 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  219 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 219 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 219 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 260 (accept_3_2 4 219 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 219 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 219 260 (accept_3_2 1 219 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219
  260)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 218 260 (Eq.refl Bool.true) (allA_succ_of_gcd 42 218 260
  2 21 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  218 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 218 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 218 260 2 20 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 218 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 218 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 218 260 2 19 109 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 218 260 (accept_3_2 37 218 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 218 260 2 18 109 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 218 260
  (Polychromatic418967fa.accept_11_2_9_7_1_124 35 218 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 218 260 2 17 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 218 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 218 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 218 260 2 16 109 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 218 260 (accept_3_2 31 218 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 218 260 2 15 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 218 260 (Polychromatic418967fa.accept_12_5_2_8_1_172
  29 218 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 218 260 2 14 109 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 218 260
  (Polychromatic418967fa.accept_11_5_9_7_1_411 27 218 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 218 260 2 13 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 218 260 (accept_3_2 25 218 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 218 260 2 12 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 218 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 218 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 218 260 2 11 109 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 218 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 218 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 218 260 2 10 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 218 260 (accept_3_2 19 218 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 218 260 2 9 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 218 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 218 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 218 260 2 8 109 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 218 260
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 218 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 218 260 2 7 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 218 260 (accept_3_2 13 218 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 218 260 2 6 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 218 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 218 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 218 260 2 5 109 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 218 260
  (Polychromatic418967fa.accept_17_9_14_5_1_1555 9 218 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 218 260 2 4 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 218 260 (accept_3_2 7 218 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 218 260 2 3 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 218 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 218 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 218 260 2 2 109 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 218 260
  (Polychromatic418967fa.accept_9_3_2_8_1_108 3 218 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 218 260 2 1 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 218 260 (accept_3_2 1 218 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  260))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 217 260 (Eq.refl Bool.true) (allA_of_3_0 44 217 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 216 260 (Eq.refl Bool.true) (allA_succ_of_gcd 44 216 260 4 11
  54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 216 260
  (accept_3_2 43 216 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 216 260 2 21 108 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 216 260
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 41 216 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 216 260 4 10 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 216 260 (Polychromatic418967fa.accept_16_7_8_4_1_689 39 216 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 216 260 2 19 108 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 216 260 (accept_3_2 37 216 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 216 260 4 9 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 216 260 (Polychromatic418967fa.accept_14_7_6_8_1_2856
  35 216 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 216 260 2 17 108 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 216 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 216 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 216 260 4 8 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 216 260 (accept_3_2 31 216 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  216 260 2 15 108 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 216 260 (Polychromatic418967fa.accept_15_14_6_5_1_7215 29 216 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 216 260 4 7 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 216 260 (Polychromatic418967fa.accept_15_12_6_5_1_1275
  27 216 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 216 260 2 13 108 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 216 260
  (accept_3_2 25 216 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 216 260 4 6 54 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 216 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 216 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 216 260 2 11 108 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 216 260 (Polychromatic418967fa.accept_14_7_6_8_1_2856 21 216 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 216 260 4 5 54 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 216 260 (accept_3_2 19 216 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 216 260 2 9 108 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 216 260
  (Polychromatic418967fa.accept_16_1_8_4_1_4334 17 216 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 216 260 4 4 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 216 260 (Polychromatic418967fa.accept_16_15_8_4_1_1355 15 216 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 216 260 2 7 108 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 216 260 (accept_3_2 13 216 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 216 260 4 3 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 216 260 (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 216
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 216 260 2 5 108 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 216 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 216 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 216 260 4 2 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 216 260 (accept_3_2 7 216 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 216
  260 2 3 108 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  216 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 216 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 216 260 4 1 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 216 260 (Polychromatic418967fa.accept_15_3_6_5_1_2079 3 216 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 216 260 2 1 108 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 216 260 (accept_3_2 1 216 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 216 260))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 215 260
  (Eq.refl Bool.true) (allA_succ_of_gcd 45 215 260 5 9 43 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 215 260 (Polychromatic418967fa.accept_16_12_7_4_1_687 44 215 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 215 260 (accept_3_2 43 215 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 215 260 (Polychromatic418967fa.accept_19_4_6_13_1_6335 42 215
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 215 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 215 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 215 260 5 8 43 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 215 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 215 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 215 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 215 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 215 260 (accept_3_2 37 215 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 215 260
  (Polychromatic418967fa.accept_19_17_6_13_1_6334 36 215 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 215 260 5 7 43 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 215 260 (accept_3_2 34 215 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 215 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 215 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 215 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 215 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 215 260 (accept_3_2 31 215 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 215 260 5 6 43 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 215 260
  (Polychromatic418967fa.accept_16_13_7_4_1_3248 29 215 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 215 260 (accept_3_2 28 215 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 215 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 215 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 215 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 215 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 215 260 5 5 43 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 215 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 215 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 215 260 (Polychromatic418967fa.accept_11_1_6_7_1_116 23 215 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 215 260 (accept_3_2 22 215 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 215 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 215 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 215 260 5 4 43 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 215 260 (accept_3_2 19 215 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 215 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 215 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 215 260 (accept_3_2 16 215 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  215 260 5 3 43 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 215 260 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 215 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 215 260 (accept_3_2 13 215 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 215 260 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 215 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 215 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 215 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 215 260 5 2 43 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 215 260
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 215 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 215 260 (Polychromatic418967fa.accept_16_8_7_4_1_2217 8 215 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 260 (accept_3_2 7 215 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 215 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 215 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 215 260 5 1 43 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 215 260 (accept_3_2 4 215 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 215 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 215 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 215 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 215 260 (accept_3_2 1 215 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215
  260)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 214 260 (Eq.refl Bool.true) (allA_of_3_0 47 214 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 213 260 (Eq.refl Bool.true) (allA_succ_of_accept 47 213 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 213 260 (accept_3_2 46 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 213 260 (Polychromatic418967fa.accept_19_7_4_13_1_6319 45 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 213 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 213 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 213 260 (accept_3_2 43 213 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 213 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 213 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 213 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 213 260 (accept_3_2 40 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 213 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 213 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 213 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 260 (accept_3_2 37 213 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 213 260 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 213 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 213 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 213 260 (accept_3_2 34 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 213 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 213 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 213 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 260 (accept_3_2 31 213 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 213 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 213 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 213 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 213 260 (accept_3_2 28 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 213 260 (Polychromatic418967fa.accept_19_8_4_13_1_4912 27 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 213 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 213 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 260 (accept_3_2 25 213 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 213 260 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 213 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 213 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 213 260 (accept_3_2 22 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 213 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 213 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 213 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 260 (accept_3_2 19 213 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 213 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 213 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 213 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 213 260 (accept_3_2 16 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 213 260 (Polychromatic418967fa.accept_16_15_5_4_1_6678 15 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 213 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 213 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 260 (accept_3_2 13 213 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 213 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 213 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 213 260 (accept_3_2 10 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  213 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 213 260 (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 213 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 260 (accept_3_2 7 213 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 213 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 213 260 (accept_3_2 4 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  213 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 213 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 213 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 213 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 260 (accept_3_2 1 213 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 213 260)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 212 260 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 212 260 4 12 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 212 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 212 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 212 260 2 23 106 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 212 260
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 212 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 212 260 4 11 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 212 260 (accept_3_2 43 212 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 212 260 2 21 106 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 212 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 212 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 212 260 4 10 53 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 212 260
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 212 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 212 260 2 19 106 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 212 260 (accept_3_2 37 212 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 212 260 4 9 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 212 260 (Polychromatic418967fa.accept_19_16_3_13_1_11816 35 212 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 212 260 2 17 106 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 212 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 212 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 212 260 4 8 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 212 260 (accept_3_2 31 212 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  212 260 2 15 106 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 212 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 212 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 212 260 4 7 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 212 260 (Polychromatic418967fa.accept_7_6_2_1_1_214 27
  212 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 212 260 2 13 106 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 212 260
  (accept_3_2 25 212 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 212 260 4 6 53 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 212 260
  (Polychromatic418967fa.accept_18_5_14_8_1_2966 23 212 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 212 260 2 11 106 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 212 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 212 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 212 260 4 5 53 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 212 260 (accept_3_2 19 212 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 212 260 2 9 106 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 212 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 17
  212 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 212 260 4 4 53 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 212 260
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 212 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 212 260 2 7 106 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 212 260 (accept_3_2 13 212 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 212 260 4 3 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 212 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 212 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 212 260 2 5 106 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 212 260 (Polychromatic418967fa.accept_19_9_3_13_1_2300
  9 212 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 212 260 4 2 53 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 212 260 (accept_3_2 7
  212 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 212 260 2 3 106 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 212 260
  (Polychromatic418967fa.accept_18_5_14_8_1_2966 5 212 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 212 260 4 1 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 212 260 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 212 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 212 260 2 1 106 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 212 260 (accept_3_2 1 212 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 212 260))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 211 260
  (Eq.refl Bool.true) (allA_of_3_0 50 211 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 210 260 (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 210 260 10 5 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 210 260 (accept_3_2 49 210 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 210 260 2 24 105 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 210 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 210 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 210 260 2 23 105 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 210 260 5 9 42 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 210 260 2 22 105 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 210 260 (accept_3_2 43 210 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 210 260 2 21 105 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 210 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 210 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 210 260 10 4 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 210 260 (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 210 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 210 260 2 19 105 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 210 260 (accept_3_2 37 210 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 210 260 2 18 105 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 210 260 5 7 42 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 210 260 2 17 105 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 210 260
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 210 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 210 260 2 16 105 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 210 260 (accept_3_2 31 210 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 210 260 10 3 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 210 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 210 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 210 260 2 14 105 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 210 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 210 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 210 260 2 13 105 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 210 260 5 5 42 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 210 260 2 12 105 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 210 260 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 210 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 210 260 2 11 105 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 210 260
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 210 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 210 260 10 2 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 210 260 (accept_3_2 19 210 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 210 260 2 9 105 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 210 260 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 210 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 210 260 2 8 105 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 210 260 5 3 42 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 210 260 2 7 105 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 210 260 (accept_3_2 13
  210 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 210 260 2 6 105 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 210 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 210 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 210 260 10 1 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 210 260 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 210 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 210 260 2 4 105 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 210 260 (accept_3_2 7 210 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 210 260 2 3 105 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 210 260 5 1 42 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 210 260 2 2 105 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 210 260
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 210 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 210 260 2 1 105 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 210 260 (accept_3_2 1 210 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210
  260))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 209 260 (Eq.refl Bool.true) (allA_succ_of_accept
  51 209 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 209 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 209 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 209 260 (accept_3_2 49 209 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 209 260 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 209 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 209 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 209 260 (accept_3_2 46 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 209 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 209 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 209 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 209 260 (accept_3_2 43 209 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 209 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 209 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 209 260
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 209 260 (accept_3_2 40 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 209 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 209 260 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 209 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 209 260 (accept_3_2 37 209 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 209 260 (Polychromatic418967fa.accept_15_6_14_5_1_2976 36 209
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 209 260
  (Polychromatic418967fa.accept_14_7_13_8_1_2067 35 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 209 260 (accept_3_2 34 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 209 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 209 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 209 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 209 260 (accept_3_2 31 209 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 209 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 209 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 209 260
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 209 260 (accept_3_2 28 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 209 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 209 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 209 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 209 260 (accept_3_2 25 209 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 209 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 209 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 209 260
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 209 260 (accept_3_2 22 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 209 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 209 260 (Polychromatic418967fa.accept_23_20_2_7_1_15892 20 209 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 209 260 (accept_3_2 19 209 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 209 260 (Polychromatic418967fa.accept_23_18_2_7_1_9297 18 209
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 260
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 209 260 (accept_3_2 16 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 209 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 209 260 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 209 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 260 (accept_3_2 13 209 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 209 260 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 209 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 209 260
  (Polychromatic418967fa.accept_21_11_20_8_1_8403 11 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 209 260 (accept_3_2 10 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 209 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 209 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 260 (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 209
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 260 (accept_3_2 7 209 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 260 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  209 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 209 260
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 209 260 (accept_3_2 4 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  209 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 209 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 209 260 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 209 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 260 (accept_3_2 1 209 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 209 260)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 208 260
  (Eq.refl Bool.true) (allA_of_3_0 53 208 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 207 260 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 207 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 207 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 207 260 (accept_3_2 52 207 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 207 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 207 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 207 260
  (Polychromatic418967fa.accept_27_23_18_17_1_12038 50 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 207 260 (accept_3_2 49 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 207 260 (Polychromatic418967fa.accept_27_21_18_17_1_15891 48 207 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 207 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 47
  207 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 207 260 (accept_3_2 46
  207 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 207 260
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 207 260 (Polychromatic418967fa.accept_16_12_15_4_1_5422 44 207 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 260 (accept_3_2 43 207 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 207 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 207 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 207 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 207 260 (accept_3_2 40 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 207 260 (Polychromatic418967fa.accept_15_9_12_5_1_1267 39 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 207 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 207 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 260 (accept_3_2 37 207 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 207 260 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 207 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 207 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 207 260 (accept_3_2 34 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 207 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 207 260 (Polychromatic418967fa.accept_14_4_11_8_1_2034 32 207 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 260 (accept_3_2 31 207 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 207 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 207
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 207 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 207 260 (accept_3_2 28 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 207 260 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 207 260 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 207 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 260 (accept_3_2 25 207 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 207 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 207 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 207 260 (accept_3_2 22 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 207 260 (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 207 260 (Polychromatic418967fa.accept_22_20_9_18_1_8087 20 207 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 260 (accept_3_2 19 207 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 207 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 207
  260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 207 260 (accept_3_2 16 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 207 260 (Polychromatic418967fa.accept_19_15_17_13_1_4901 15 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 260 (Polychromatic418967fa.accept_16_14_15_4_1_3268 14 207 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 260 (accept_3_2 13 207 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 260 (Polychromatic418967fa.accept_7_5_4_1_1_412
  12 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 207 260 (accept_3_2 10 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  207 260 (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 207 260 (Polychromatic418967fa.accept_15_8_12_5_1_2987 8 207 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 260 (accept_3_2 7 207 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 260 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 207 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 260
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 207 260 (accept_3_2 4 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  207 260 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 207 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 207 260 (Polychromatic418967fa.accept_11_2_9_7_1_124 2 207 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 260 (accept_3_2 1 207 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 207 260)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 206 260
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 206 260 2 27 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 206 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 206 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 206 260 2 26 103 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 206 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 206 260 2 25 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 206 260 (accept_3_2 49 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 206 260 2 24 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 206 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 206 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 206 260 2 23 103 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 206 260
  (Polychromatic418967fa.accept_21_3_17_8_1_8402 45 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 206 260 2 22 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 206 260 (accept_3_2 43 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 206 260 2 21 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 206 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 206 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 206 260 2 20 103 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 206 260
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 206 260 2 19 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 206 260 (accept_3_2 37 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 206 260 2 18 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 206 260 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 206 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 206 260 2 17 103 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 206 260
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 206 260 2 16 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 206 260 (accept_3_2 31 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 206 260 2 15 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 206 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 206 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 206 260 2 14 103 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 206 260
  (Polychromatic418967fa.accept_25_2_6_10_1_3309 27 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 206 260 2 13 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 206 260 (accept_3_2 25 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 206 260 2 12 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 206 260 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 206 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 206 260 2 11 103 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 206 260
  (Polychromatic418967fa.accept_15_6_11_5_1_168 21 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 206 260 2 10 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 206 260 (accept_3_2 19 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 206 260 2 9 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 206 260 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 206 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 206 260 2 8 103 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 206 260
  (Polychromatic418967fa.accept_11_4_8_7_1_819 15 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 206 260 2 7 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 206 260 (accept_3_2 13 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 206 260 2 6 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 206 260 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 206 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 206 260 2 5 103 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 206 260
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 206 260 2 4 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 206 260 (accept_3_2 7 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 206 260 2 3 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 206 260 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 206 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 260 2 2 103 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 260
  (Polychromatic418967fa.accept_17_3_2_5_1_2556 3 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 260 2 1 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 260 (accept_3_2 1 206 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 205 260 (Eq.refl Bool.true) (allA_of_3_0 56
  205 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 204 260 (Eq.refl Bool.true) (allA_succ_of_gcd 56 204
  260 4 14 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55
  204 260 (accept_3_2 55 204 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 204 260 2 27 102 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 204 260
  (Polychromatic418967fa.accept_16_5_12_4_1_4325 53 204 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 204 260 4 13 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 204 260 (Polychromatic418967fa.accept_16_3_12_4_1_170 51 204 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 204 260 2 25 102 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 204 260 (accept_3_2 49 204 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 204 260 4 12 51 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 204 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 204 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 204 260 2 23 102 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 204 260 (Polychromatic418967fa.accept_11_1_6_7_1_116 45 204 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 204 260 4 11 51 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 204 260 (accept_3_2 43 204 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 204 260 2 21 102 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 204 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 41
  204 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 204 260 4 10 51 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 204 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 204 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 204 260 2 19 102 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 204 260 (accept_3_2 37 204 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 204 260 4 9 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 204 260 (Polychromatic418967fa.accept_16_3_12_4_1_170 35 204 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 204 260 2 17 102 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 204 260 (Polychromatic418967fa.accept_15_3_9_5_1_2082
  33 204 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 204 260 4 8 51 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 204 260
  (accept_3_2 31 204 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 204 260 2 15 102 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 204 260
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 204 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 204 260 4 7 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 204 260 (Polychromatic418967fa.accept_15_12_9_5_1_2973 27 204 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 204 260 2 13 102 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 204 260 (accept_3_2 25 204 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 204 260 4 6 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 204 260 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 204 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 204 260 2 11 102 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 204 260
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 204 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 204 260 4 5 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 204 260 (accept_3_2 19 204 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  204 260 2 9 102 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 204 260 (Polychromatic418967fa.accept_16_1_12_4_1_695 17 204 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 204 260 4 4 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 204 260
  (Polychromatic418967fa.accept_16_15_12_4_1_4324 15 204 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 204 260 2 7 102 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 204 260 (accept_3_2 13 204 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 204 260 4 3 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 204 260 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 204 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 204 260 2 5 102 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 204 260 (Polychromatic418967fa.accept_16_9_12_4_1_3255
  9 204 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 204 260 4 2 51 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 260 (accept_3_2 7
  204 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 260 2 3 102 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 260
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 204 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 204 260 4 1 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 204 260 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 204 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 204 260 2 1 102 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 204 260 (accept_3_2 1 204 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 204 260))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 203 260
  (Eq.refl Bool.true) (allA_succ_of_accept 57 203 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 203 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 203 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 203 260 (accept_3_2 55 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 203 260 (Polychromatic418967fa.accept_16_6_11_4_1_635 54 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 203 260 (Polychromatic418967fa.accept_11_9_5_7_1_815 53 203 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 203 260 (accept_3_2 52 203 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 203 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 203 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 203 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 203 260 (accept_3_2 49 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 203 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 203 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 203 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 203 260 (accept_3_2 46 203 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 203 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 203 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 203 260
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 44 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 203 260 (accept_3_2 43 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 203 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 203 260 (Polychromatic418967fa.accept_14_13_7_8_1_677 41 203 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 203 260 (accept_3_2 40 203 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 203 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 203 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 203 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 203 260 (accept_3_2 37 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 203 260 (Polychromatic418967fa.accept_17_2_16_5_1_1584 36 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 203 260 (Polychromatic418967fa.accept_17_1_16_5_1_3670 35 203 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 203 260 (accept_3_2 34 203 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 203 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 203 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 203 260
  (Polychromatic418967fa.accept_18_14_5_8_1_1880 32 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 203 260 (accept_3_2 31 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 203 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 203 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 203 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 203 260 (accept_3_2 28 203 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 203 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 203 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 203 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 203 260 (accept_3_2 25 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 203 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 203 260 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 203 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 203 260 (accept_3_2 22 203 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 203 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 203 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 203 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 203 260 (accept_3_2 19 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 203 260 (Polychromatic418967fa.accept_15_3_8_5_1_2105 18 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 203 260 (Polychromatic418967fa.accept_18_17_5_8_1_1898 17 203 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 203 260 (accept_3_2 16 203 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 203 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 203 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 203 260
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 203 260 (accept_3_2 13 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 203 260 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 203 260 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 203 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 260 (accept_3_2 10 203 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 203 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 203 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 260
  (Polychromatic418967fa.accept_16_8_11_4_1_3290 8 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 203 260 (accept_3_2 7 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  203 260 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 203 260 (Polychromatic418967fa.accept_21_5_14_8_1_6818 5 203 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 260 (accept_3_2 4 203 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 260 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 203 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 260
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 203 260 (accept_3_2 1 203 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203
  260)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 202 260 (Eq.refl Bool.true) (allA_of_3_0
  59 202 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 201 260 (Eq.refl Bool.true) (allA_succ_of_accept 59
  201 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 201 260 (accept_3_2 58 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 201 260 (Polychromatic418967fa.accept_15_12_6_5_1_1275 57 201 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 201 260 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 201 260
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 201 260 (accept_3_2 55 201 260
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 201 260
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 201 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 201 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 201 260 (accept_3_2 52 201 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 201 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 201 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 201 260 (Polychromatic418967fa.accept_9_5_3_8_1_316
  50 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 201 260 (accept_3_2 49
  201 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 201 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 201 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 201 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 201 260 (accept_3_2 46 201 260 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 201 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 201 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 201 260
  (Polychromatic418967fa.accept_15_14_6_5_1_7215 44 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 201 260 (accept_3_2 43 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 201 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 201 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 201 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 201 260 (accept_3_2 40 201 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 201 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 201 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 201 260
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 201 260 (accept_3_2 37 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 201 260 (Polychromatic418967fa.accept_17_2_14_5_1_2575 36 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 201 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 201 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 260 (accept_3_2 34 201 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 201 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 201 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 201 260
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 201 260 (accept_3_2 31 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 201 260 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 201 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 201 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 260 (accept_3_2 28 201 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 201 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 201 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 201 260
  (Polychromatic418967fa.accept_11_4_3_7_1_828 26 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 201 260 (accept_3_2 25 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 201 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 201 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 201 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 260 (accept_3_2 22 201 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 260 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 201 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 201 260
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 201 260 (accept_3_2 19 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 201 260 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 201 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 201 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 260 (accept_3_2 16 201 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 260 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 201 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 260
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 201 260 (accept_3_2 13 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 201 260 (Polychromatic418967fa.accept_15_12_6_5_1_1275 12 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 201 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 201 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 260 (accept_3_2 10 201 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 260 (Polychromatic418967fa.accept_17_9_14_5_1_1555 9 201 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 260
  (Polychromatic418967fa.accept_16_8_9_4_1_630 8 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 201 260 (accept_3_2 7 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  201 260 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 201 260 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 201 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 260 (accept_3_2 4 201 260 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 260 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 201 260 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 260
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 201 260 (accept_3_2 1 201 260 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201
  260))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_260_segment_001)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


