-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_020
-- name    : RealPinwheel_FiveSixths_WitnessD7_020
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:27:00.590395+00:00
-- url     : https://prove2.me/theorems/d8c5d48a-dfd6-4b23-bdc3-25e6af6ac4a6
-- title:
--   Exact witness block D7_020
-- statement:
--   These exact witnesses represent words 197 through 211 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 197–211; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_020_196 : CycleWitness 7 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (6))) (.branch 11 (.leaf (2)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (5)) (.leaf (0))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (5))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (6))) (.branch 28 (.leaf (0)) (.leaf (4)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (5)) (.leaf (2)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (5))) (.branch 41 (.leaf (2)) (.leaf (1))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (6))) (.branch 45 (.leaf (3)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 50 (.leaf (5)) (.leaf (0))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (3)) (.leaf (1))) (.branch 54 (.leaf (0)) (.leaf (4)))) (.branch 57 (.branch 56 (.leaf (2)) (.leaf (5))) (.branch 58 (.leaf (0)) (.leaf (1))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (3)) (.leaf (6))) (.branch 62 (.leaf (0)) (.leaf (4)))) (.branch 65 (.branch 64 (.leaf (2)) (.leaf (1))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (5)) (.leaf (3)))))))))
  code := certificateD7_196
  counts := ![(.branch 32 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 51 (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.branch 47 (.leaf (12)) (.leaf (13))))) (.branch 58 (.branch 54 (.leaf (14)) (.leaf (15))) (.branch 62 (.leaf (16)) (.branch 66 (.leaf (17)) (.leaf (18))))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 41 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 37 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 45 (.leaf (5)) (.leaf (6))) (.branch 60 (.leaf (7)) (.branch 68 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 67 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-25))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-41)) (.leaf (-42)))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 37 (.leaf (-6)) (.branch 52 (.leaf (-7)) (.leaf (-8))))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (-3))) (.branch 40 (.leaf (-4)) (.branch 57 (.leaf (-5)) (.leaf (-6))))),
  (.branch 10 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 59 (.branch 36 (.leaf (-25)) (.branch 55 (.leaf (-24)) (.leaf (-22)))) (.branch 63 (.leaf (-20)) (.branch 67 (.leaf (-18)) (.leaf (-9))))),
  (.branch 60 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 65 (.branch 19 (.leaf (-42)) (.branch 57 (.leaf (-40)) (.leaf (-36)))) (.branch 66 (.leaf (-27)) (.branch 67 (.leaf (-18)) (.leaf (-9))))),
  (.branch 53 (.leaf (-8)) (.branch 61 (.leaf (-4)) (.leaf (0)))),
  (.branch 65 (.branch 64 (.leaf (-10)) (.leaf (-8))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 58 (.leaf (-6)) (.leaf (-5))),
  (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_020_197 : CycleWitness 7 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (6)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (5)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (6)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (1)) (.leaf (3))) (.branch 28 (.leaf (0)) (.leaf (4)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (5)) (.leaf (3)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (6)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (3))) (.branch 41 (.leaf (4)) (.leaf (1))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (2)) (.leaf (0))) (.branch 45 (.leaf (5)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (3)) (.leaf (0))) (.branch 49 (.leaf (2)) (.branch 50 (.leaf (1)) (.leaf (4))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (6)) (.leaf (0))) (.branch 54 (.leaf (3)) (.leaf (2)))) (.branch 57 (.branch 56 (.leaf (1)) (.leaf (0))) (.branch 58 (.leaf (5)) (.leaf (2))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (1)) (.leaf (3))) (.branch 62 (.leaf (0)) (.leaf (4)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (2))) (.branch 66 (.leaf (1)) (.branch 67 (.leaf (6)) (.leaf (3)))))))))
  code := certificateD7_197
  counts := ![(.branch 30 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 48 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 57 (.branch 53 (.leaf (12)) (.leaf (13))) (.branch 62 (.leaf (14)) (.branch 64 (.leaf (15)) (.leaf (16))))))),
  (.branch 32 (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 50 (.branch 42 (.branch 36 (.leaf (7)) (.leaf (8))) (.branch 46 (.leaf (9)) (.leaf (10)))) (.branch 60 (.branch 56 (.leaf (11)) (.leaf (12))) (.branch 66 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 40 (.leaf (5)) (.branch 47 (.leaf (6)) (.leaf (7)))) (.branch 61 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 67 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-24))) (.branch 30 (.leaf (-27)) (.branch 64 (.leaf (-38)) (.leaf (-48))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 50 (.leaf (-4)) (.leaf (-5)))),
  (.branch 25 (.branch 3 (.leaf (0)) (.leaf (-14))) (.branch 59 (.leaf (-20)) (.leaf (-24)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (-9))) (.branch 51 (.leaf (-12)) (.leaf (-13)))),
  (.branch 45 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 58 (.leaf (-11)) (.leaf (-12)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 66 (.branch 65 (.leaf (-48)) (.leaf (-41))) (.branch 67 (.leaf (-34)) (.leaf (-27)))),
  (.branch 61 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3)))),
  (.branch 66 (.branch 60 (.leaf (-24)) (.leaf (-23))) (.branch 67 (.leaf (-18)) (.leaf (-13)))),
  (.branch 48 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.branch 62 (.leaf (-1)) (.leaf (0))))),
  (.branch 65 (.branch 52 (.leaf (-13)) (.branch 64 (.leaf (-12)) (.leaf (-10)))) (.branch 66 (.leaf (-8)) (.branch 67 (.leaf (-6)) (.leaf (-4))))),
  (.branch 63 (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-11))) (.branch 61 (.leaf (-10)) (.branch 62 (.leaf (-9)) (.leaf (-8))))) (.branch 65 (.branch 64 (.leaf (-7)) (.leaf (-6))) (.branch 66 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 53 (.leaf (-4)) (.leaf (-3)))]
def witnessD7_020_198 : CycleWitness 7 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (5)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (4))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (4))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (0)) (.leaf (5)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (3))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (6)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (4))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (3))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (2))) (.branch 54 (.leaf (1)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (5)) (.leaf (3))) (.branch 58 (.leaf (0)) (.leaf (2))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (1)) (.leaf (0))) (.branch 62 (.leaf (3)) (.leaf (0)))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (4))) (.branch 66 (.leaf (2)) (.branch 67 (.leaf (0)) (.leaf (6)))))))))
  code := certificateD7_198
  counts := ![(.branch 33 (.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 27 (.leaf (9)) (.branch 29 (.leaf (10)) (.leaf (11)))))) (.branch 49 (.branch 41 (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14)))) (.branch 43 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17))))) (.branch 58 (.branch 52 (.leaf (18)) (.branch 55 (.leaf (19)) (.leaf (20)))) (.branch 63 (.branch 61 (.leaf (21)) (.leaf (22))) (.branch 67 (.leaf (23)) (.leaf (24))))))),
  (.branch 30 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 50 (.branch 40 (.branch 36 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 60 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 64 (.leaf (13)) (.leaf (14)))))),
  (.branch 32 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 39 (.leaf (5)) (.branch 46 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4))))),
  (.branch 34 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 45 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 68 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 29 (.branch 1 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))) (.branch 43 (.leaf (-4)) (.branch 63 (.leaf (-5)) (.leaf (-6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 10 (.leaf (-4)) (.branch 44 (.leaf (-5)) (.leaf (-6))))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (-9)) (.leaf (-11)))),
  (.branch 28 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 23 (.leaf (-8)) (.leaf (-9)))) (.branch 57 (.branch 42 (.leaf (-12)) (.leaf (-14))) (.branch 62 (.leaf (-15)) (.leaf (-18))))),
  (.branch 14 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.branch 56 (.leaf (-35)) (.leaf (-36)))),
  (.branch 22 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 64 (.leaf (-6)) (.leaf (-5))),
  (.branch 66 (.branch 65 (.leaf (-6)) (.leaf (-5))) (.branch 67 (.leaf (-4)) (.leaf (-3)))),
  (.branch 60 (.leaf (-11)) (.branch 67 (.leaf (-10)) (.leaf (-5)))),
  (.branch 65 (.branch 63 (.leaf (-18)) (.branch 64 (.leaf (-17)) (.leaf (-16)))) (.branch 66 (.leaf (-15)) (.branch 67 (.leaf (-14)) (.leaf (-13))))),
  (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))),
  (.branch 62 (.branch 59 (.branch 57 (.leaf (-36)) (.branch 58 (.leaf (-33)) (.leaf (-30)))) (.branch 60 (.leaf (-27)) (.branch 61 (.leaf (-24)) (.leaf (-21))))) (.branch 65 (.branch 63 (.leaf (-18)) (.branch 64 (.leaf (-15)) (.leaf (-12)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 23 (.leaf (-2)) (.branch 46 (.leaf (-1)) (.leaf (0))))]
def witnessD7_020_199 : CycleWitness 7 where
  length := 67
  word := (.branch 35 (.branch 18 (.branch 10 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (2))) (.branch 9 (.leaf (0)) (.leaf (1))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (5)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (0))) (.branch 17 (.leaf (1)) (.leaf (2)))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (4))) (.branch 22 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (0))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (5)) (.leaf (6))) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (0)) (.leaf (4))))))) (.branch 51 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (2)) (.leaf (0))) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (5)) (.leaf (3))) (.branch 42 (.leaf (0)) (.leaf (1))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (2))) (.branch 46 (.leaf (6)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (4)) (.leaf (0))) (.branch 50 (.leaf (1)) (.leaf (0)))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (3)) (.leaf (0))) (.branch 54 (.leaf (5)) (.leaf (2)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (0)) (.leaf (4))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (3)) (.leaf (0))) (.branch 62 (.leaf (6)) (.leaf (0)))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (2))) (.branch 66 (.leaf (0)) (.leaf (5))))))))
  code := certificateD7_199
  counts := ![(.branch 32 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 19 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 20 (.leaf (9)) (.leaf (10)))) (.branch 27 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.leaf (14)))))) (.branch 49 (.branch 39 (.branch 34 (.leaf (15)) (.branch 37 (.leaf (16)) (.leaf (17)))) (.branch 44 (.branch 42 (.leaf (18)) (.leaf (19))) (.branch 47 (.leaf (20)) (.leaf (21))))) (.branch 58 (.branch 53 (.branch 51 (.leaf (22)) (.leaf (23))) (.branch 56 (.leaf (24)) (.leaf (25)))) (.branch 63 (.branch 61 (.leaf (26)) (.leaf (27))) (.branch 66 (.leaf (28)) (.leaf (29))))))),
  (.branch 31 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 38 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 36 (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 55 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 65 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 40 (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 54 (.leaf (3)) (.branch 67 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))) (.branch 22 (.branch 20 (.leaf (-18)) (.leaf (-20))) (.branch 53 (.leaf (-22)) (.leaf (-23))))),
  (.branch 3 (.leaf (0)) (.branch 43 (.leaf (-19)) (.leaf (-23)))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (-7))) (.branch 45 (.leaf (-13)) (.leaf (-15)))),
  (.branch 33 (.branch 4 (.leaf (0)) (.branch 23 (.leaf (-13)) (.leaf (-17)))) (.branch 41 (.leaf (-18)) (.branch 60 (.leaf (-23)) (.leaf (-27))))),
  (.branch 48 (.branch 7 (.leaf (0)) (.leaf (-7))) (.branch 59 (.leaf (-8)) (.leaf (-11)))),
  (.branch 13 (.leaf (0)) (.branch 40 (.leaf (-1)) (.leaf (-2)))),
  (.branch 12 (.leaf (0)) (.branch 62 (.leaf (-19)) (.leaf (-20))))]
  high := ![(.branch 59 (.branch 54 (.leaf (-23)) (.leaf (-22))) (.branch 64 (.leaf (-21)) (.leaf (-18)))),
  (.branch 58 (.branch 44 (.leaf (-23)) (.branch 51 (.leaf (-22)) (.leaf (-21)))) (.branch 65 (.leaf (-20)) (.branch 66 (.leaf (-15)) (.leaf (-10))))),
  (.branch 56 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 66 (.leaf (-13)) (.leaf (-9)))),
  (.branch 63 (.branch 61 (.leaf (-27)) (.branch 62 (.leaf (-25)) (.leaf (-23)))) (.branch 65 (.branch 64 (.leaf (-21)) (.leaf (-19))) (.branch 66 (.leaf (-17)) (.leaf (-15))))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-11)) (.leaf (-10))) (.branch 62 (.leaf (-9)) (.leaf (-8)))) (.branch 65 (.branch 64 (.leaf (-7)) (.leaf (-6))) (.branch 66 (.leaf (-5)) (.leaf (-4))))),
  (.branch 55 (.leaf (-2)) (.branch 56 (.leaf (-1)) (.leaf (0)))),
  (.branch 64 (.branch 63 (.leaf (-20)) (.leaf (-16))) (.branch 65 (.leaf (-12)) (.branch 66 (.leaf (-8)) (.leaf (-4)))))]
def witnessD7_020_200 : CycleWitness 7 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (0))) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (2)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 40 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (5))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (1)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (2))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (0)) (.leaf (2)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (6)) (.leaf (2)))))))))
  code := certificateD7_200
  counts := ![(.branch 31 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 18 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 20 (.leaf (9)) (.leaf (10)))) (.branch 27 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 29 (.leaf (13)) (.leaf (14)))))) (.branch 49 (.branch 40 (.branch 36 (.branch 34 (.leaf (15)) (.leaf (16))) (.branch 38 (.leaf (17)) (.leaf (18)))) (.branch 45 (.branch 42 (.leaf (19)) (.leaf (20))) (.branch 47 (.leaf (21)) (.leaf (22))))) (.branch 58 (.branch 53 (.branch 51 (.leaf (23)) (.leaf (24))) (.branch 56 (.leaf (25)) (.leaf (26)))) (.branch 62 (.branch 60 (.leaf (27)) (.leaf (28))) (.branch 64 (.leaf (29)) (.leaf (30))))))),
  (.branch 30 (.branch 13 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 37 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 33 (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 39 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 61 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1))),
  (.branch 65 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-6)) (.leaf (-7)))) (.branch 7 (.leaf (-8)) (.branch 9 (.leaf (-9)) (.leaf (-10))))),
  (.branch 26 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 15 (.leaf (-4)) (.leaf (-5)))) (.branch 48 (.branch 37 (.leaf (-6)) (.leaf (-7))) (.branch 59 (.leaf (-8)) (.leaf (-9))))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-12))),
  (.branch 21 (.leaf (0)) (.leaf (-45))),
  (.branch 43 (.leaf (0)) (.leaf (-23))),
  (.branch 65 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 65 (.leaf (-10)) (.leaf (-5))),
  (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 43 (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (-45)) (.leaf (-44))) (.branch 24 (.leaf (-43)) (.branch 25 (.leaf (-42)) (.leaf (-41))))) (.branch 29 (.branch 27 (.leaf (-40)) (.branch 28 (.leaf (-39)) (.leaf (-38)))) (.branch 30 (.leaf (-37)) (.branch 31 (.leaf (-36)) (.leaf (-35)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (-34)) (.leaf (-33))) (.branch 35 (.leaf (-32)) (.branch 36 (.leaf (-31)) (.leaf (-30))))) (.branch 40 (.branch 38 (.leaf (-29)) (.branch 39 (.leaf (-28)) (.leaf (-27)))) (.branch 41 (.leaf (-26)) (.branch 42 (.leaf (-25)) (.leaf (-24))))))) (.branch 54 (.branch 48 (.branch 45 (.branch 44 (.leaf (-23)) (.leaf (-22))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19))))) (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 54 (.branch 48 (.branch 45 (.branch 44 (.leaf (-23)) (.leaf (-22))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19))))) (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_020_201 : CycleWitness 7 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (3))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (1)) (.leaf (5))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (1)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (3)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (2))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (6))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (1)) (.leaf (2)))))))))
  code := certificateD7_201
  counts := ![(.branch 31 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))) (.branch 47 (.branch 39 (.branch 34 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14)))) (.branch 42 (.leaf (15)) (.branch 45 (.leaf (16)) (.leaf (17))))) (.branch 56 (.branch 50 (.leaf (18)) (.branch 53 (.leaf (19)) (.leaf (20)))) (.branch 61 (.branch 58 (.leaf (21)) (.leaf (22))) (.branch 64 (.leaf (23)) (.leaf (24))))))),
  (.branch 32 (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 26 (.leaf (9)) (.branch 29 (.leaf (10)) (.leaf (11)))))) (.branch 48 (.branch 40 (.branch 35 (.leaf (12)) (.branch 37 (.leaf (13)) (.leaf (14)))) (.branch 43 (.leaf (15)) (.branch 46 (.leaf (16)) (.leaf (17))))) (.branch 57 (.branch 51 (.leaf (18)) (.branch 54 (.leaf (19)) (.leaf (20)))) (.branch 62 (.branch 59 (.leaf (21)) (.leaf (22))) (.branch 65 (.leaf (23)) (.leaf (24))))))),
  (.branch 33 (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1))),
  (.branch 63 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 19 (.leaf (0)) (.leaf (-47))),
  (.branch 41 (.leaf (0)) (.leaf (-25))),
  (.branch 63 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 62 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.branch 60 (.leaf (-6)) (.branch 63 (.leaf (-5)) (.leaf (-4)))),
  (.branch 61 (.leaf (-1)) (.leaf (0))),
  (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 30 (.branch 24 (.branch 21 (.branch 20 (.leaf (-47)) (.leaf (-46))) (.branch 22 (.leaf (-45)) (.branch 23 (.leaf (-44)) (.leaf (-43))))) (.branch 27 (.branch 25 (.leaf (-42)) (.branch 26 (.leaf (-41)) (.leaf (-40)))) (.branch 28 (.leaf (-39)) (.branch 29 (.leaf (-38)) (.leaf (-37)))))) (.branch 36 (.branch 33 (.branch 31 (.leaf (-36)) (.branch 32 (.leaf (-35)) (.leaf (-34)))) (.branch 34 (.leaf (-33)) (.branch 35 (.leaf (-32)) (.leaf (-31))))) (.branch 39 (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-29)) (.leaf (-28)))) (.branch 40 (.leaf (-27)) (.branch 41 (.leaf (-26)) (.leaf (-25))))))) (.branch 54 (.branch 48 (.branch 45 (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22)))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19))))) (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 53 (.branch 47 (.branch 44 (.branch 42 (.leaf (-25)) (.branch 43 (.leaf (-24)) (.leaf (-23)))) (.branch 45 (.leaf (-22)) (.branch 46 (.leaf (-21)) (.leaf (-20))))) (.branch 50 (.branch 48 (.leaf (-19)) (.branch 49 (.leaf (-18)) (.leaf (-17)))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-15)) (.leaf (-14)))))) (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_020_202 : CycleWitness 7 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (5)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (2))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (6)) (.leaf (0))) (.branch 40 (.leaf (3)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (4))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (0))) (.branch 48 (.leaf (1)) (.leaf (5)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (2))) (.branch 52 (.leaf (3)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (4)) (.leaf (1))) (.branch 56 (.leaf (0)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (3))) (.branch 60 (.leaf (6)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (2))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (4)) (.leaf (3)))))))))
  code := certificateD7_202
  counts := ![(.branch 31 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))) (.branch 47 (.branch 39 (.branch 34 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14)))) (.branch 42 (.leaf (15)) (.branch 45 (.leaf (16)) (.leaf (17))))) (.branch 56 (.branch 50 (.leaf (18)) (.branch 53 (.leaf (19)) (.leaf (20)))) (.branch 61 (.branch 58 (.leaf (21)) (.leaf (22))) (.branch 64 (.leaf (23)) (.leaf (24))))))),
  (.branch 29 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 40 (.leaf (5)) (.branch 46 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-14))) (.branch 41 (.leaf (-16)) (.leaf (-17)))),
  (.branch 30 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 63 (.leaf (-10)) (.leaf (-11)))),
  (.branch 19 (.branch 13 (.leaf (0)) (.leaf (-1))) (.branch 52 (.leaf (-3)) (.leaf (-4)))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 16 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 62 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.branch 56 (.branch 42 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 64 (.branch 63 (.leaf (-14)) (.leaf (-11))) (.branch 65 (.leaf (-8)) (.leaf (-5))))),
  (.branch 64 (.leaf (-11)) (.branch 65 (.leaf (-8)) (.leaf (-5)))),
  (.branch 53 (.leaf (-4)) (.branch 60 (.leaf (-3)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))) (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.leaf (-10))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_020_203 : CycleWitness 7 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (5))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (3)) (.leaf (0))) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (4))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (1)) (.leaf (3))) (.branch 40 (.leaf (0)) (.leaf (4))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (6))) (.branch 48 (.leaf (1)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (3)) (.leaf (0))) (.branch 52 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (4))) (.branch 56 (.leaf (1)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (5)) (.leaf (0))) (.branch 60 (.leaf (1)) (.leaf (3)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (2))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (0)) (.leaf (6)))))))))
  code := certificateD7_203
  counts := ![(.branch 32 (.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 26 (.leaf (9)) (.branch 29 (.leaf (10)) (.leaf (11)))))) (.branch 49 (.branch 40 (.branch 34 (.leaf (12)) (.branch 37 (.leaf (13)) (.leaf (14)))) (.branch 43 (.leaf (15)) (.branch 46 (.leaf (16)) (.leaf (17))))) (.branch 57 (.branch 51 (.leaf (18)) (.branch 54 (.leaf (19)) (.leaf (20)))) (.branch 62 (.branch 59 (.leaf (21)) (.leaf (22))) (.branch 65 (.leaf (23)) (.leaf (24))))))),
  (.branch 31 (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 38 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 44 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 30 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 47 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 26 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 34 (.leaf (-10)) (.branch 59 (.leaf (-12)) (.leaf (-13))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 11 (.leaf (-16)) (.branch 44 (.leaf (-26)) (.leaf (-35))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 36 (.leaf (-7)) (.branch 53 (.leaf (-9)) (.leaf (-10))))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (-10))) (.branch 55 (.leaf (-14)) (.leaf (-17)))),
  (.branch 14 (.leaf (0)) (.branch 33 (.leaf (-10)) (.leaf (-15)))),
  (.branch 47 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 60 (.leaf (-13)) (.branch 63 (.leaf (-12)) (.leaf (-11)))),
  (.branch 53 (.branch 45 (.leaf (-35)) (.branch 49 (.leaf (-34)) (.leaf (-33)))) (.branch 61 (.branch 57 (.leaf (-32)) (.leaf (-31))) (.branch 65 (.leaf (-30)) (.leaf (-24))))),
  (.branch 64 (.branch 54 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-7)))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-17)) (.leaf (-16))) (.branch 58 (.leaf (-15)) (.branch 59 (.leaf (-14)) (.leaf (-13))))) (.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-11)) (.leaf (-10)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7)))))),
  (.branch 61 (.branch 59 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 60 (.leaf (-13)) (.leaf (-12)))) (.branch 63 (.branch 62 (.leaf (-11)) (.leaf (-10))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7)))))),
  (.branch 48 (.leaf (-1)) (.leaf (0)))]
def witnessD7_020_204 : CycleWitness 7 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (6)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (3)) (.leaf (1))) (.branch 40 (.leaf (6)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (1))) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (1)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (2)) (.leaf (0))) (.branch 60 (.leaf (1)) (.leaf (6)))) (.branch 63 (.branch 62 (.leaf (3)) (.leaf (0))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (1)) (.leaf (4)))))))))
  code := certificateD7_204
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 32 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 51 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 26 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-14)) (.leaf (-18)))) (.branch 37 (.leaf (-22)) (.branch 59 (.leaf (-24)) (.leaf (-28))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.branch 14 (.leaf (-9)) (.leaf (-10))))) (.branch 43 (.branch 35 (.leaf (-11)) (.branch 39 (.leaf (-12)) (.leaf (-13)))) (.branch 47 (.leaf (-14)) (.branch 51 (.leaf (-15)) (.leaf (-16)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 52 (.leaf (-17)) (.leaf (-20)))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-13))) (.branch 21 (.leaf (-14)) (.branch 29 (.leaf (-15)) (.leaf (-16))))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 28 (.leaf (-15)) (.leaf (-16)))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 64 (.branch 60 (.leaf (-28)) (.leaf (-27))) (.branch 65 (.leaf (-22)) (.leaf (-17)))),
  (.branch 52 (.leaf (-16)) (.branch 61 (.leaf (-15)) (.leaf (-13)))),
  (.branch 59 (.branch 53 (.leaf (-20)) (.leaf (-18))) (.branch 65 (.leaf (-16)) (.leaf (-11)))),
  (.branch 64 (.branch 63 (.leaf (-16)) (.leaf (-12))) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_020_205 : CycleWitness 7 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (5)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (3)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (6))) (.branch 23 (.leaf (1)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (0))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (2)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (4)) (.leaf (2))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (6)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (3)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (4))) (.branch 52 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (5))) (.branch 56 (.leaf (1)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (3))) (.branch 60 (.leaf (1)) (.leaf (2)))) (.branch 63 (.branch 62 (.leaf (4)) (.leaf (0))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (2)) (.leaf (6)))))))))
  code := certificateD7_205
  counts := ![(.branch 30 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 63 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.branch 64 (.leaf (15)) (.leaf (16))))))),
  (.branch 32 (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 49 (.branch 41 (.branch 36 (.leaf (8)) (.leaf (9))) (.branch 45 (.leaf (10)) (.leaf (11)))) (.branch 57 (.branch 53 (.leaf (12)) (.leaf (13))) (.branch 61 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 9 (.leaf (-26)) (.leaf (-27)))) (.branch 21 (.branch 17 (.leaf (-28)) (.leaf (-29))) (.branch 25 (.leaf (-30)) (.leaf (-31))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 10 (.leaf (-18)) (.branch 14 (.leaf (-19)) (.leaf (-20))))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 64 (.branch 59 (.leaf (-31)) (.leaf (-24))) (.branch 65 (.leaf (-16)) (.leaf (-8)))),
  (.branch 48 (.leaf (-20)) (.branch 65 (.leaf (-16)) (.leaf (-8)))),
  (.branch 37 (.leaf (-9)) (.leaf (-8))),
  (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_020_206 : CycleWitness 7 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (6)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (4))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (6)) (.leaf (0))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (1)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (3)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (1)) (.leaf (4))) (.branch 40 (.leaf (6)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (5)) (.leaf (2))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (4))) (.branch 48 (.leaf (0)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (0)) (.leaf (3)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (4))) (.branch 56 (.leaf (0)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (5)) (.leaf (0))) (.branch 60 (.leaf (1)) (.leaf (3)))) (.branch 63 (.branch 62 (.leaf (6)) (.leaf (0))) (.branch 64 (.leaf (4)) (.branch 65 (.leaf (2)) (.leaf (5)))))))))
  code := certificateD7_206
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 32 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 54 (.leaf (7)) (.branch 60 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 38 (.leaf (-13)) (.branch 60 (.leaf (-14)) (.leaf (-15))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 49 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-21)) (.leaf (-22)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-9))) (.branch 22 (.leaf (-10)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 64 (.branch 60 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 63 (.branch 61 (.leaf (-15)) (.branch 62 (.leaf (-13)) (.leaf (-11)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-7)) (.leaf (-5))))),
  (.branch 50 (.leaf (-7)) (.branch 58 (.leaf (-6)) (.leaf (-5)))),
  (.branch 63 (.branch 45 (.leaf (-22)) (.branch 62 (.leaf (-20)) (.leaf (-16)))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 56 (.leaf (-11)) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_020_207 : CycleWitness 7 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (4)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (3)) (.leaf (6))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (6))) (.branch 40 (.leaf (1)) (.leaf (2))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (3))) (.branch 44 (.leaf (4)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (3)) (.leaf (5))) (.branch 52 (.leaf (0)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (4))) (.branch 56 (.leaf (0)) (.leaf (3))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (1)) (.leaf (2))) (.branch 60 (.leaf (0)) (.leaf (6)))) (.branch 63 (.branch 62 (.leaf (3)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (2)) (.leaf (4)))))))))
  code := certificateD7_207
  counts := ![(.branch 31 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 30 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 32 (.branch 14 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 37 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 36 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 48 (.leaf (-15)) (.leaf (-18)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 25 (.leaf (-12)) (.branch 58 (.leaf (-14)) (.leaf (-15))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 41 (.leaf (-14)) (.leaf (-20)))),
  (.branch 29 (.branch 3 (.leaf (0)) (.leaf (-15))) (.branch 62 (.leaf (-19)) (.leaf (-22)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 18 (.leaf (0)) (.branch 39 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 57 (.branch 49 (.leaf (-18)) (.branch 53 (.leaf (-17)) (.leaf (-16)))) (.branch 61 (.leaf (-15)) (.branch 65 (.leaf (-14)) (.leaf (-10))))),
  (.branch 64 (.branch 59 (.leaf (-15)) (.leaf (-14))) (.branch 65 (.leaf (-10)) (.leaf (-6)))),
  (.branch 48 (.branch 42 (.leaf (-20)) (.leaf (-19))) (.branch 54 (.leaf (-18)) (.branch 60 (.leaf (-17)) (.leaf (-16))))),
  (.branch 64 (.branch 63 (.leaf (-22)) (.leaf (-18))) (.branch 65 (.leaf (-14)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 58 (.branch 54 (.branch 52 (.branch 29 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_020_208 : CycleWitness 7 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (4))) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (2))) (.branch 23 (.leaf (6)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (4)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (2)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (4)) (.leaf (6)))) (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (3)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (4)) (.leaf (0))) (.branch 44 (.leaf (2)) (.leaf (5)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (3))) (.branch 48 (.leaf (0)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (6)) (.leaf (4))) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (2))) (.branch 56 (.leaf (5)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (2))) (.branch 60 (.leaf (4)) (.leaf (3)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (6)) (.branch 65 (.leaf (2)) (.leaf (3)))))))))
  code := certificateD7_208
  counts := ![(.branch 29 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 48 (.branch 39 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 43 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 30 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 40 (.leaf (5)) (.branch 47 (.leaf (6)) (.leaf (7)))) (.branch 61 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 12 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-26)) (.leaf (-29)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 26 (.leaf (-3)) (.branch 59 (.leaf (-7)) (.leaf (-10))))),
  (.branch 33 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 42 (.leaf (-25)) (.leaf (-30)))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (-19))) (.branch 56 (.leaf (-20)) (.leaf (-23)))),
  (.branch 12 (.leaf (0)) (.branch 23 (.leaf (-3)) (.leaf (-8))))]
  high := ![(.branch 63 (.branch 44 (.leaf (-29)) (.leaf (-28))) (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-14)) (.leaf (-7))))),
  (.branch 64 (.branch 58 (.leaf (-7)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 60 (.leaf (-10)) (.leaf (-9))),
  (.branch 41 (.branch 34 (.leaf (-3)) (.leaf (-2))) (.branch 48 (.leaf (-1)) (.leaf (0)))),
  (.branch 62 (.branch 52 (.branch 43 (.leaf (-30)) (.leaf (-29))) (.branch 61 (.leaf (-28)) (.leaf (-25)))) (.branch 64 (.branch 63 (.leaf (-22)) (.leaf (-19))) (.branch 65 (.leaf (-16)) (.leaf (-13))))),
  (.branch 61 (.branch 58 (.branch 57 (.leaf (-23)) (.leaf (-21))) (.branch 59 (.leaf (-19)) (.branch 60 (.leaf (-17)) (.leaf (-15))))) (.branch 63 (.branch 62 (.leaf (-13)) (.leaf (-11))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-7)) (.leaf (-5)))))),
  (.branch 51 (.leaf (-8)) (.branch 65 (.leaf (-7)) (.leaf (-5))))]
def witnessD7_020_209 : CycleWitness 7 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (1)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (1)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (6)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (1))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (5)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (4)) (.leaf (3))) (.branch 52 (.leaf (0)) (.leaf (6)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (2))) (.branch 56 (.leaf (0)) (.leaf (3))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (1)) (.leaf (0))) (.branch 60 (.leaf (5)) (.leaf (4)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (0))) (.branch 64 (.leaf (3)) (.branch 65 (.leaf (1)) (.leaf (6)))))))))
  code := certificateD7_209
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 32 (.branch 14 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 38 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 40 (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 53 (.leaf (3)) (.branch 66 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))) (.branch 47 (.branch 36 (.leaf (-5)) (.leaf (-6))) (.branch 58 (.leaf (-7)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.leaf (-23))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-8))) (.branch 24 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (-31))) (.branch 33 (.leaf (-32)) (.branch 46 (.leaf (-33)) (.leaf (-34))))),
  (.branch 13 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 64 (.branch 60 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 59 (.leaf (-8)) (.leaf (-7))),
  (.branch 63 (.branch 36 (.leaf (-23)) (.branch 56 (.leaf (-22)) (.leaf (-20)))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 58 (.leaf (-12)) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 62 (.branch 47 (.leaf (-34)) (.branch 61 (.leaf (-30)) (.leaf (-25)))) (.branch 64 (.branch 63 (.leaf (-20)) (.leaf (-15))) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 14 (.leaf (-1)) (.leaf (0)))]
def witnessD7_020_210 : CycleWitness 7 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (5))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (6)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (1)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (1)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (3)) (.leaf (6))) (.branch 40 (.leaf (4)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (1))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (4)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (3))) (.branch 52 (.leaf (0)) (.leaf (4)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (2))) (.branch 56 (.leaf (0)) (.leaf (3))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (1)) (.leaf (0))) (.branch 60 (.leaf (4)) (.leaf (6)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (0))) (.branch 64 (.leaf (3)) (.branch 65 (.leaf (1)) (.leaf (4)))))))))
  code := certificateD7_210
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 32 (.branch 14 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 38 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 40 (.leaf (5)) (.branch 46 (.leaf (6)) (.leaf (7)))) (.branch 60 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))) (.branch 47 (.branch 36 (.leaf (-5)) (.leaf (-6))) (.branch 58 (.leaf (-7)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.leaf (-23))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-8))) (.branch 24 (.leaf (-11)) (.leaf (-12)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 64 (.branch 60 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 59 (.leaf (-8)) (.leaf (-7))),
  (.branch 63 (.branch 36 (.leaf (-23)) (.branch 56 (.leaf (-22)) (.leaf (-20)))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 58 (.leaf (-12)) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.branch 47 (.leaf (-1)) (.leaf (0))),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_020 : Fin 15 → CycleWitness 7 := ![witnessD7_020_196, witnessD7_020_197, witnessD7_020_198, witnessD7_020_199, witnessD7_020_200, witnessD7_020_201, witnessD7_020_202, witnessD7_020_203, witnessD7_020_204, witnessD7_020_205, witnessD7_020_206, witnessD7_020_207, witnessD7_020_208, witnessD7_020_209, witnessD7_020_210]
end RealPinwheel.FiveSixths


