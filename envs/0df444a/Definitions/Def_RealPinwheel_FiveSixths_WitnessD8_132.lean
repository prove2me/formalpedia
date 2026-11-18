-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_132
-- name    : RealPinwheel_FiveSixths_WitnessD8_132
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:52:29.692718+00:00
-- url     : https://prove2.me/theorems/51aea04a-5658-43b0-b8df-69d4ff738cbc
-- title:
--   Exact witness block D8_132
-- statement:
--   These exact witnesses represent words 1047 through 1059 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1047–1059; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_132_1046 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (6)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (7))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (3))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (6)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (5)) (.leaf (2))) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (4)) (.leaf (7)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (3)) (.leaf (0)))) (.branch 42 (.branch 41 (.leaf (2)) (.leaf (5))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (6)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (3)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (4)))) (.branch 51 (.branch 50 (.leaf (1)) (.leaf (0))) (.branch 52 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (7))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (5)) (.leaf (0)))) (.branch 60 (.branch 59 (.leaf (2)) (.leaf (3))) (.branch 61 (.leaf (1)) (.branch 62 (.leaf (0)) (.leaf (6)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (4)) (.leaf (2))) (.branch 66 (.leaf (0)) (.leaf (3)))) (.branch 69 (.branch 68 (.leaf (1)) (.leaf (0))) (.branch 70 (.leaf (2)) (.branch 71 (.leaf (5)) (.leaf (7)))))))))
  code := certificateD8_1046
  counts := ![(.branch 33 (.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))) (.branch 51 (.branch 40 (.branch 37 (.leaf (10)) (.leaf (11))) (.branch 44 (.leaf (12)) (.branch 48 (.leaf (13)) (.leaf (14))))) (.branch 62 (.branch 55 (.leaf (15)) (.branch 58 (.leaf (16)) (.leaf (17)))) (.branch 66 (.leaf (18)) (.branch 69 (.leaf (19)) (.leaf (20))))))),
  (.branch 32 (.branch 14 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 38 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 61 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))) (.branch 52 (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))) (.branch 65 (.branch 59 (.leaf (9)) (.leaf (10))) (.branch 70 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 39 (.leaf (5)) (.branch 46 (.leaf (6)) (.leaf (7)))) (.branch 60 (.leaf (8)) (.branch 67 (.leaf (9)) (.leaf (10)))))),
  (.branch 35 (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 42 (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 57 (.leaf (3)) (.branch 71 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.branch 72 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-21)) (.leaf (-22)))) (.branch 24 (.leaf (-23)) (.branch 31 (.leaf (-24)) (.leaf (-25))))),
  (.branch 6 (.leaf (0)) (.branch 49 (.leaf (-42)) (.leaf (-43)))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 70 (.branch 59 (.leaf (-16)) (.leaf (-15))) (.branch 71 (.leaf (-10)) (.leaf (-5)))),
  (.branch 69 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1))))),
  (.branch 71 (.leaf (-2)) (.leaf (-1))),
  (.branch 69 (.branch 68 (.leaf (-25)) (.leaf (-20))) (.branch 70 (.leaf (-15)) (.branch 71 (.leaf (-10)) (.leaf (-5))))),
  (.branch 67 (.branch 65 (.branch 50 (.leaf (-43)) (.leaf (-40))) (.branch 66 (.leaf (-35)) (.leaf (-30)))) (.branch 69 (.branch 68 (.leaf (-25)) (.leaf (-20))) (.branch 70 (.leaf (-15)) (.branch 71 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 14 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))),
  (.branch 67 (.branch 65 (.branch 64 (.leaf (-9)) (.leaf (-8))) (.branch 66 (.leaf (-7)) (.leaf (-6)))) (.branch 69 (.branch 68 (.leaf (-5)) (.leaf (-4))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_132_1047 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (7)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (4))) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (6)) (.leaf (3))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (5)) (.leaf (0))) (.branch 30 (.leaf (4)) (.leaf (7)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (6)) (.branch 35 (.leaf (3)) (.leaf (2)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (0)))) (.branch 42 (.branch 41 (.leaf (5)) (.leaf (1))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (3)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (6)) (.leaf (0))) (.branch 48 (.leaf (1)) (.leaf (7)))) (.branch 51 (.branch 50 (.leaf (4)) (.leaf (0))) (.branch 52 (.leaf (5)) (.branch 53 (.leaf (1)) (.leaf (2))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (3))) (.branch 57 (.leaf (1)) (.leaf (0)))) (.branch 60 (.branch 59 (.leaf (6)) (.leaf (4))) (.branch 61 (.leaf (0)) (.branch 62 (.leaf (2)) (.leaf (1)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (5)) (.leaf (0))) (.branch 66 (.leaf (3)) (.leaf (7)))) (.branch 69 (.branch 68 (.leaf (1)) (.leaf (0))) (.branch 70 (.leaf (6)) (.branch 71 (.leaf (4)) (.leaf (2)))))))))
  code := certificateD8_1047
  counts := ![(.branch 33 (.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))) (.branch 51 (.branch 40 (.branch 37 (.leaf (10)) (.leaf (11))) (.branch 43 (.leaf (12)) (.branch 47 (.leaf (13)) (.leaf (14))))) (.branch 61 (.branch 55 (.leaf (15)) (.branch 58 (.leaf (16)) (.leaf (17)))) (.branch 65 (.leaf (18)) (.branch 69 (.leaf (19)) (.leaf (20))))))),
  (.branch 32 (.branch 12 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))) (.branch 53 (.branch 42 (.branch 38 (.leaf (7)) (.leaf (8))) (.branch 48 (.leaf (9)) (.leaf (10)))) (.branch 63 (.branch 57 (.leaf (11)) (.leaf (12))) (.branch 68 (.leaf (13)) (.leaf (14)))))),
  (.branch 36 (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.branch 72 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 66 (.leaf (6)) (.leaf (7))))),
  (.branch 39 (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))) (.branch 60 (.branch 50 (.leaf (4)) (.leaf (5))) (.branch 71 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 59 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 70 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 67 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))) (.branch 43 (.branch 25 (.leaf (-12)) (.leaf (-13))) (.branch 61 (.leaf (-14)) (.leaf (-15))))),
  (.branch 21 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-10)) (.leaf (-14)))) (.branch 42 (.leaf (-17)) (.branch 57 (.leaf (-18)) (.leaf (-21))))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-37))),
  (.branch 9 (.leaf (0)) (.branch 39 (.leaf (-7)) (.leaf (-13)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 66 (.branch 62 (.leaf (-15)) (.leaf (-14))) (.branch 70 (.leaf (-13)) (.branch 71 (.leaf (-10)) (.leaf (-7))))),
  (.branch 69 (.branch 58 (.leaf (-21)) (.leaf (-20))) (.branch 70 (.leaf (-17)) (.branch 71 (.leaf (-14)) (.leaf (-11))))),
  (.branch 63 (.leaf (-1)) (.leaf (0))),
  (.branch 67 (.branch 25 (.branch 4 (.leaf (-37)) (.leaf (-36))) (.branch 46 (.leaf (-35)) (.leaf (-34)))) (.branch 69 (.branch 68 (.leaf (-29)) (.leaf (-24))) (.branch 70 (.leaf (-19)) (.branch 71 (.leaf (-14)) (.leaf (-9)))))),
  (.branch 40 (.leaf (-13)) (.branch 61 (.leaf (-12)) (.leaf (-9)))),
  (.branch 68 (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-7))) (.branch 67 (.leaf (-6)) (.leaf (-5)))) (.branch 70 (.branch 69 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1))))),
  (.branch 71 (.leaf (-2)) (.leaf (-1))),
  (.branch 69 (.branch 68 (.leaf (-5)) (.leaf (-4))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_132_1048 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (6)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (4)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (7)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (3)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (5)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (6)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (2)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (3)) (.leaf (0)))) (.branch 42 (.branch 41 (.leaf (5)) (.leaf (1))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (7)) (.leaf (2)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (4)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (3)) (.leaf (1))) (.branch 52 (.leaf (0)) (.branch 53 (.leaf (5)) (.leaf (2))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (6)) (.leaf (0)))) (.branch 60 (.branch 59 (.leaf (4)) (.leaf (1))) (.branch 61 (.leaf (0)) (.branch 62 (.leaf (3)) (.leaf (2)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (5)) (.leaf (0)))) (.branch 69 (.branch 68 (.leaf (7)) (.leaf (1))) (.branch 70 (.leaf (0)) (.branch 71 (.leaf (4)) (.leaf (2)))))))))
  code := certificateD8_1048
  counts := ![(.branch 34 (.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 28 (.leaf (9)) (.branch 31 (.leaf (10)) (.leaf (11)))))) (.branch 52 (.branch 43 (.branch 37 (.leaf (12)) (.branch 40 (.leaf (13)) (.leaf (14)))) (.branch 46 (.leaf (15)) (.branch 49 (.leaf (16)) (.leaf (17))))) (.branch 61 (.branch 55 (.leaf (18)) (.branch 58 (.leaf (19)) (.leaf (20)))) (.branch 67 (.branch 64 (.leaf (21)) (.leaf (22))) (.branch 70 (.leaf (23)) (.leaf (24))))))),
  (.branch 33 (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 51 (.branch 42 (.branch 38 (.leaf (8)) (.leaf (9))) (.branch 47 (.leaf (10)) (.leaf (11)))) (.branch 60 (.branch 56 (.leaf (12)) (.leaf (13))) (.branch 65 (.leaf (14)) (.branch 69 (.leaf (15)) (.leaf (16))))))),
  (.branch 36 (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.branch 72 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 12 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 59 (.branch 48 (.leaf (3)) (.leaf (4))) (.branch 71 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 68 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 23 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 21 (.leaf (0)) (.branch 44 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 71 (.leaf (-2)) (.leaf (-1))),
  (.branch 70 (.leaf (-6)) (.branch 71 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 67 (.branch 64 (.branch 63 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.branch 66 (.leaf (-7)) (.leaf (-6))))) (.branch 69 (.branch 68 (.leaf (-5)) (.leaf (-4))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 68 (.branch 54 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5)))) (.branch 70 (.branch 69 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1))))),
  (.branch 64 (.branch 60 (.branch 58 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 59 (.leaf (-14)) (.leaf (-13)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-11))) (.branch 63 (.leaf (-10)) (.leaf (-9))))) (.branch 68 (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-7))) (.branch 67 (.leaf (-6)) (.leaf (-5)))) (.branch 70 (.branch 69 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 70 (.branch 69 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_132_1049 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (2))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (7)) (.leaf (3))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (5)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (6))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (7))) (.branch 30 (.leaf (2)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (4)) (.leaf (0))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (1)) (.leaf (0)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (2)) (.leaf (6))) (.branch 39 (.leaf (3)) (.leaf (1)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (2))) (.branch 43 (.leaf (7)) (.branch 44 (.leaf (0)) (.leaf (1)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (4)) (.leaf (2))) (.branch 48 (.leaf (5)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (1)) (.leaf (3))) (.branch 52 (.leaf (0)) (.branch 53 (.leaf (6)) (.leaf (2))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (1)) (.leaf (4))) (.branch 57 (.leaf (0)) (.leaf (7)))) (.branch 60 (.branch 59 (.leaf (1)) (.leaf (0))) (.branch 61 (.leaf (2)) (.branch 62 (.leaf (5)) (.leaf (3)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (1)) (.leaf (0))) (.branch 66 (.leaf (2)) (.leaf (6)))) (.branch 69 (.branch 68 (.leaf (0)) (.leaf (1))) (.branch 70 (.leaf (4)) (.branch 71 (.leaf (2)) (.leaf (7)))))))))
  code := certificateD8_1049
  counts := ![(.branch 33 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 52 (.branch 41 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.branch 49 (.leaf (12)) (.leaf (13))))) (.branch 60 (.branch 57 (.leaf (14)) (.leaf (15))) (.branch 65 (.leaf (16)) (.branch 68 (.leaf (17)) (.leaf (18))))))),
  (.branch 35 (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))) (.branch 55 (.branch 45 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 50 (.leaf (10)) (.leaf (11)))) (.branch 64 (.branch 59 (.leaf (12)) (.leaf (13))) (.branch 69 (.leaf (14)) (.leaf (15)))))),
  (.branch 37 (.branch 18 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))) (.branch 54 (.branch 42 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))) (.branch 66 (.branch 61 (.leaf (9)) (.leaf (10))) (.branch 71 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 70 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 62 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 53 (.leaf (3)) (.branch 67 (.leaf (4)) (.leaf (5))))),
  (.branch 43 (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 58 (.leaf (3)) (.branch 72 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-14)) (.leaf (-17)))),
  (.branch 42 (.branch 18 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 23 (.leaf (-3)) (.leaf (-6)))) (.branch 66 (.branch 47 (.leaf (-7)) (.leaf (-10))) (.branch 71 (.leaf (-11)) (.leaf (-14))))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 32 (.branch 8 (.leaf (0)) (.leaf (-5))) (.branch 56 (.leaf (-7)) (.leaf (-9)))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (-47))) (.branch 62 (.leaf (-49)) (.leaf (-50)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (-22))) (.branch 38 (.leaf (-24)) (.leaf (-26)))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 70 (.branch 69 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1)))),
  (.branch 65 (.branch 60 (.leaf (-17)) (.leaf (-16))) (.branch 70 (.leaf (-15)) (.branch 71 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-14)),
  (.branch 67 (.branch 65 (.branch 64 (.leaf (-9)) (.leaf (-8))) (.branch 66 (.leaf (-7)) (.leaf (-6)))) (.branch 69 (.branch 68 (.leaf (-5)) (.leaf (-4))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.leaf (-9)) (.branch 71 (.leaf (-8)) (.leaf (-7)))),
  (.branch 67 (.branch 64 (.branch 63 (.leaf (-50)) (.leaf (-45))) (.branch 65 (.leaf (-40)) (.branch 66 (.leaf (-35)) (.leaf (-30))))) (.branch 69 (.branch 68 (.leaf (-25)) (.leaf (-20))) (.branch 70 (.leaf (-15)) (.branch 71 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 69 (.branch 39 (.leaf (-26)) (.branch 68 (.leaf (-25)) (.leaf (-20)))) (.branch 70 (.leaf (-15)) (.branch 71 (.leaf (-10)) (.leaf (-5))))),
  (.branch 15 (.leaf (-2)) (.branch 44 (.leaf (-1)) (.leaf (0))))]
def witnessD8_132_1050 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (6)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (0)) (.leaf (7)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (4)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (6)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (3)) (.leaf (2)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (5)) (.branch 44 (.leaf (0)) (.leaf (4)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (2)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (3)))) (.branch 51 (.branch 50 (.leaf (7)) (.leaf (1))) (.branch 52 (.leaf (0)) (.branch 53 (.leaf (2)) (.leaf (4))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (3)) (.leaf (2)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (5)) (.branch 62 (.leaf (0)) (.leaf (6)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (2)) (.leaf (1))) (.branch 66 (.leaf (0)) (.leaf (3)))) (.branch 69 (.branch 68 (.leaf (4)) (.leaf (1))) (.branch 70 (.leaf (0)) (.branch 71 (.leaf (2)) (.leaf (7)))))))))
  code := certificateD8_1050
  counts := ![(.branch 34 (.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))) (.branch 52 (.branch 41 (.branch 37 (.leaf (10)) (.leaf (11))) (.branch 44 (.leaf (12)) (.branch 48 (.leaf (13)) (.leaf (14))))) (.branch 62 (.branch 55 (.leaf (15)) (.branch 59 (.leaf (16)) (.leaf (17)))) (.branch 66 (.leaf (18)) (.branch 70 (.leaf (19)) (.leaf (20))))))),
  (.branch 33 (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 51 (.branch 42 (.branch 38 (.leaf (8)) (.leaf (9))) (.branch 47 (.leaf (10)) (.leaf (11)))) (.branch 60 (.branch 56 (.leaf (12)) (.leaf (13))) (.branch 65 (.leaf (14)) (.branch 69 (.leaf (15)) (.leaf (16))))))),
  (.branch 35 (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 53 (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))) (.branch 64 (.branch 58 (.leaf (9)) (.leaf (10))) (.branch 71 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 67 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 36 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3)))),
  (.branch 50 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 72 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (-4))) (.branch 54 (.leaf (-8)) (.leaf (-11)))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 14 (.leaf (0)) (.branch 36 (.leaf (-12)) (.leaf (-16)))),
  (.branch 50 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 67 (.branch 63 (.leaf (-14)) (.leaf (-12))) (.branch 71 (.leaf (-10)) (.leaf (-5)))),
  (.branch 70 (.leaf (-6)) (.branch 71 (.leaf (-4)) (.leaf (-2)))),
  (.branch 65 (.leaf (-2)) (.leaf (-1))),
  (.branch 69 (.branch 58 (.leaf (-6)) (.branch 68 (.leaf (-5)) (.leaf (-4)))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1))))),
  (.branch 69 (.branch 55 (.leaf (-11)) (.leaf (-10))) (.branch 70 (.leaf (-9)) (.branch 71 (.leaf (-8)) (.leaf (-7))))),
  (.branch 66 (.branch 63 (.branch 62 (.leaf (-11)) (.leaf (-10))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7))))) (.branch 69 (.branch 67 (.leaf (-6)) (.branch 68 (.leaf (-5)) (.leaf (-4)))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 67 (.branch 64 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 65 (.leaf (-14)) (.branch 66 (.leaf (-13)) (.leaf (-12))))) (.branch 69 (.branch 68 (.leaf (-11)) (.leaf (-10))) (.branch 70 (.leaf (-9)) (.branch 71 (.leaf (-8)) (.leaf (-7)))))),
  (.branch 51 (.leaf (-2)) (.branch 52 (.leaf (-1)) (.leaf (0))))]
def witnessD8_132_1051 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (3))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (2)) (.leaf (6))) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (2))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (4)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (7)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (1)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (3)) (.leaf (1)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (4))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (5)) (.leaf (1)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (0)) (.leaf (3))) (.branch 48 (.leaf (2)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (1)) (.leaf (3))) (.branch 52 (.leaf (2)) (.branch 53 (.leaf (0)) (.leaf (4))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (1)) (.leaf (6))) (.branch 57 (.leaf (2)) (.leaf (0)))) (.branch 60 (.branch 59 (.leaf (3)) (.leaf (1))) (.branch 61 (.leaf (0)) (.branch 62 (.leaf (2)) (.leaf (3)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (1)) (.leaf (0))) (.branch 66 (.leaf (4)) (.leaf (2)))) (.branch 69 (.branch 68 (.leaf (7)) (.leaf (1))) (.branch 70 (.leaf (0)) (.branch 71 (.leaf (3)) (.leaf (2)))))))))
  code := certificateD8_1051
  counts := ![(.branch 34 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))) (.branch 53 (.branch 41 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.branch 49 (.leaf (12)) (.leaf (13))))) (.branch 61 (.branch 58 (.leaf (14)) (.leaf (15))) (.branch 65 (.leaf (16)) (.branch 70 (.leaf (17)) (.leaf (18))))))),
  (.branch 36 (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))) (.branch 55 (.branch 45 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 50 (.leaf (10)) (.leaf (11)))) (.branch 64 (.branch 60 (.leaf (12)) (.leaf (13))) (.branch 69 (.leaf (14)) (.leaf (15)))))),
  (.branch 38 (.branch 19 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))) (.branch 57 (.branch 48 (.branch 43 (.leaf (8)) (.leaf (9))) (.branch 52 (.leaf (10)) (.leaf (11)))) (.branch 67 (.branch 62 (.leaf (12)) (.leaf (13))) (.branch 72 (.leaf (14)) (.leaf (15)))))),
  (.branch 35 (.branch 15 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 39 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))) (.branch 63 (.branch 59 (.leaf (9)) (.leaf (10))) (.branch 71 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 56 (.leaf (1)) (.leaf (2)))),
  (.branch 32 (.leaf (0)) (.branch 68 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 27 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-4)) (.leaf (-6)))) (.branch 51 (.branch 39 (.leaf (-8)) (.leaf (-10))) (.branch 63 (.leaf (-12)) (.leaf (-14))))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-28))),
  (.branch 20 (.leaf (0)) (.leaf (-16))),
  (.branch 32 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 66 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1)))),
  (.branch 70 (.branch 65 (.leaf (-16)) (.leaf (-15))) (.branch 71 (.leaf (-10)) (.leaf (-5)))),
  (.branch 58 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.branch 68 (.leaf (-1)) (.leaf (0))))),
  (.branch 64 (.leaf (-14)) (.leaf (-13))),
  (.branch 69 (.branch 67 (.leaf (-6)) (.branch 68 (.leaf (-5)) (.leaf (-4)))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 51 (.branch 47 (.branch 45 (.leaf (-28)) (.branch 46 (.leaf (-27)) (.leaf (-26)))) (.branch 49 (.branch 48 (.leaf (-25)) (.leaf (-24))) (.branch 50 (.leaf (-23)) (.leaf (-22))))) (.branch 54 (.branch 52 (.leaf (-21)) (.branch 53 (.leaf (-20)) (.leaf (-19)))) (.branch 56 (.branch 55 (.leaf (-18)) (.leaf (-17))) (.branch 57 (.leaf (-16)) (.leaf (-15)))))) (.branch 65 (.branch 61 (.branch 59 (.leaf (-14)) (.branch 60 (.leaf (-13)) (.leaf (-12)))) (.branch 63 (.branch 62 (.leaf (-11)) (.leaf (-10))) (.branch 64 (.leaf (-9)) (.leaf (-8))))) (.branch 68 (.branch 66 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5)))) (.branch 70 (.branch 69 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 64 (.branch 60 (.branch 58 (.branch 57 (.leaf (-16)) (.leaf (-15))) (.branch 59 (.leaf (-14)) (.leaf (-13)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-11))) (.branch 63 (.leaf (-10)) (.leaf (-9))))) (.branch 68 (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-7))) (.branch 67 (.leaf (-6)) (.leaf (-5)))) (.branch 70 (.branch 69 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 70 (.branch 69 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_132_1052 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (7)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (3)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (5)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (6))) (.branch 30 (.leaf (2)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (2)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (3)) (.leaf (2)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (7))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (5)) (.leaf (0)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (2)) (.leaf (4))) (.branch 48 (.leaf (1)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (3)) (.leaf (2))) (.branch 52 (.leaf (0)) (.branch 53 (.leaf (6)) (.leaf (1))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (2))) (.branch 57 (.leaf (3)) (.leaf (1)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (4))) (.branch 61 (.leaf (2)) (.branch 62 (.leaf (5)) (.leaf (0)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (1)) (.leaf (7))) (.branch 66 (.leaf (2)) (.leaf (0)))) (.branch 69 (.branch 68 (.leaf (3)) (.leaf (1))) (.branch 70 (.leaf (0)) (.branch 71 (.leaf (4)) (.leaf (2)))))))))
  code := certificateD8_1052
  counts := ![(.branch 34 (.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (7)) (.branch 31 (.leaf (8)) (.leaf (9)))))) (.branch 52 (.branch 41 (.branch 37 (.leaf (10)) (.leaf (11))) (.branch 45 (.leaf (12)) (.branch 49 (.leaf (13)) (.leaf (14))))) (.branch 63 (.branch 55 (.leaf (15)) (.branch 59 (.leaf (16)) (.leaf (17)))) (.branch 67 (.leaf (18)) (.branch 70 (.leaf (19)) (.leaf (20))))))),
  (.branch 33 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))) (.branch 54 (.branch 43 (.branch 38 (.leaf (7)) (.leaf (8))) (.branch 48 (.leaf (9)) (.leaf (10)))) (.branch 64 (.branch 58 (.leaf (11)) (.leaf (12))) (.branch 69 (.leaf (13)) (.leaf (14)))))),
  (.branch 36 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))) (.branch 56 (.branch 46 (.branch 40 (.leaf (7)) (.leaf (8))) (.branch 51 (.leaf (9)) (.leaf (10)))) (.branch 66 (.branch 61 (.leaf (11)) (.leaf (12))) (.branch 72 (.leaf (13)) (.leaf (14)))))),
  (.branch 32 (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 60 (.branch 47 (.leaf (3)) (.leaf (4))) (.branch 71 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 19 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 37 (.leaf (-9)) (.branch 55 (.leaf (-10)) (.leaf (-11))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-19)) (.leaf (-20)))) (.branch 22 (.leaf (-21)) (.branch 58 (.leaf (-23)) (.leaf (-24))))),
  (.branch 4 (.leaf (0)) (.branch 40 (.leaf (-7)) (.leaf (-8)))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 39 (.leaf (-9)) (.branch 57 (.leaf (-11)) (.leaf (-13))))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 6 (.leaf (0)) (.branch 29 (.leaf (-18)) (.leaf (-19)))),
  (.branch 17 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 56 (.leaf (-11)) (.branch 71 (.leaf (-10)) (.leaf (-7)))),
  (.branch 70 (.branch 59 (.leaf (-24)) (.leaf (-20))) (.branch 71 (.leaf (-14)) (.leaf (-8)))),
  (.branch 67 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 68 (.leaf (-1)) (.leaf (0)))),
  (.branch 69 (.branch 58 (.leaf (-13)) (.leaf (-12))) (.branch 70 (.leaf (-11)) (.branch 71 (.leaf (-10)) (.leaf (-9))))),
  (.leaf (-1)),
  (.branch 67 (.branch 64 (.branch 63 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.branch 66 (.leaf (-7)) (.leaf (-6))))) (.branch 69 (.branch 68 (.leaf (-5)) (.leaf (-4))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 62 (.branch 57 (.branch 55 (.branch 54 (.leaf (-19)) (.leaf (-18))) (.branch 56 (.leaf (-17)) (.leaf (-16)))) (.branch 59 (.branch 58 (.leaf (-15)) (.leaf (-14))) (.branch 60 (.leaf (-13)) (.branch 61 (.leaf (-12)) (.leaf (-11)))))) (.branch 67 (.branch 64 (.branch 63 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.branch 66 (.leaf (-7)) (.leaf (-6))))) (.branch 69 (.branch 68 (.leaf (-5)) (.leaf (-4))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 68 (.branch 66 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5)))) (.branch 70 (.branch 69 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_132_1053 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (7))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (6)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (5)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (4))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (1)) (.leaf (7))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (3)) (.leaf (2))) (.branch 21 (.leaf (5)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (6))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (2)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (5)) (.leaf (0))) (.branch 30 (.leaf (7)) (.leaf (4)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (6))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (5)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (6)))) (.branch 42 (.branch 41 (.leaf (2)) (.leaf (7))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (0)) (.leaf (5)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (1)) (.leaf (4))) (.branch 48 (.leaf (6)) (.leaf (2)))) (.branch 51 (.branch 50 (.leaf (0)) (.leaf (3))) (.branch 52 (.leaf (5)) (.branch 53 (.leaf (1)) (.leaf (7))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (4)) (.leaf (2))) (.branch 57 (.leaf (6)) (.leaf (0)))) (.branch 60 (.branch 59 (.leaf (3)) (.leaf (5))) (.branch 61 (.leaf (1)) (.branch 62 (.leaf (2)) (.leaf (4)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (6)) (.leaf (0))) (.branch 66 (.leaf (7)) (.leaf (3)))) (.branch 69 (.branch 68 (.leaf (1)) (.leaf (5))) (.branch 70 (.leaf (2)) (.branch 71 (.leaf (4)) (.leaf (6)))))))))
  code := certificateD8_1053
  counts := ![(.branch 29 (.branch 8 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 65 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 38 (.leaf (5)) (.branch 46 (.leaf (6)) (.leaf (7)))) (.branch 61 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 34 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 56 (.branch 41 (.leaf (5)) (.branch 49 (.leaf (6)) (.leaf (7)))) (.branch 62 (.leaf (8)) (.branch 70 (.leaf (9)) (.leaf (10)))))),
  (.branch 35 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 59 (.leaf (7)) (.branch 67 (.leaf (8)) (.leaf (9)))))),
  (.branch 39 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))) (.branch 55 (.branch 47 (.leaf (5)) (.leaf (6))) (.branch 63 (.leaf (7)) (.branch 71 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 45 (.leaf (5)) (.leaf (6))) (.branch 60 (.leaf (7)) (.branch 69 (.leaf (8)) (.leaf (9)))))),
  (.branch 40 (.branch 16 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))) (.branch 57 (.branch 48 (.leaf (5)) (.leaf (6))) (.branch 64 (.leaf (7)) (.branch 72 (.leaf (8)) (.leaf (9)))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 14 (.leaf (-20)) (.branch 50 (.leaf (-24)) (.leaf (-26))))),
  (.branch 2 (.leaf (0)) (.branch 38 (.leaf (-16)) (.leaf (-18)))),
  (.branch 26 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 62 (.leaf (-10)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 68 (.branch 66 (.branch 51 (.leaf (-26)) (.leaf (-25))) (.branch 67 (.leaf (-22)) (.leaf (-19)))) (.branch 70 (.branch 69 (.leaf (-16)) (.leaf (-13))) (.branch 71 (.leaf (-10)) (.leaf (-7))))),
  (.branch 69 (.branch 39 (.leaf (-18)) (.branch 54 (.leaf (-17)) (.leaf (-16)))) (.branch 70 (.leaf (-13)) (.branch 71 (.leaf (-10)) (.leaf (-7))))),
  (.branch 63 (.leaf (-12)) (.branch 71 (.leaf (-10)) (.leaf (-7)))),
  (.branch 69 (.branch 68 (.leaf (-5)) (.leaf (-4))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 70 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 69 (.branch 67 (.leaf (-6)) (.branch 68 (.leaf (-5)) (.leaf (-4)))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_132_1054 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (5))) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (4))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (3)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (5)) (.leaf (7)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (4)) (.leaf (3)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (5)) (.leaf (0)))) (.branch 42 (.branch 41 (.leaf (2)) (.leaf (1))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (4)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (2)) (.leaf (0))) (.branch 48 (.leaf (1)) (.leaf (6)))) (.branch 51 (.branch 50 (.leaf (5)) (.leaf (0))) (.branch 52 (.leaf (2)) (.branch 53 (.leaf (1)) (.leaf (3))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (4))) (.branch 57 (.leaf (1)) (.leaf (0)))) (.branch 60 (.branch 59 (.leaf (2)) (.leaf (5))) (.branch 61 (.leaf (0)) (.branch 62 (.leaf (3)) (.leaf (1)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (2)) (.leaf (0))) (.branch 66 (.leaf (4)) (.leaf (7)))) (.branch 69 (.branch 68 (.leaf (1)) (.leaf (0))) (.branch 70 (.leaf (2)) (.branch 71 (.leaf (5)) (.leaf (3)))))))))
  code := certificateD8_1054
  counts := ![(.branch 33 (.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))) (.branch 51 (.branch 40 (.branch 37 (.leaf (10)) (.leaf (11))) (.branch 43 (.leaf (12)) (.branch 47 (.leaf (13)) (.leaf (14))))) (.branch 61 (.branch 55 (.leaf (15)) (.branch 58 (.leaf (16)) (.leaf (17)))) (.branch 65 (.leaf (18)) (.branch 69 (.leaf (19)) (.leaf (20))))))),
  (.branch 32 (.branch 12 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))) (.branch 53 (.branch 42 (.branch 38 (.leaf (7)) (.leaf (8))) (.branch 48 (.leaf (9)) (.leaf (10)))) (.branch 63 (.branch 57 (.leaf (11)) (.leaf (12))) (.branch 68 (.leaf (13)) (.leaf (14)))))),
  (.branch 34 (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 52 (.branch 41 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))) (.branch 64 (.branch 59 (.leaf (9)) (.leaf (10))) (.branch 70 (.leaf (11)) (.leaf (12)))))),
  (.branch 36 (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.branch 72 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 66 (.leaf (6)) (.leaf (7))))),
  (.branch 39 (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))) (.branch 60 (.branch 50 (.leaf (4)) (.leaf (5))) (.branch 71 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2)))),
  (.branch 31 (.leaf (0)) (.branch 67 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))) (.branch 43 (.branch 25 (.leaf (-12)) (.leaf (-13))) (.branch 61 (.leaf (-14)) (.leaf (-15))))),
  (.branch 21 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-10)) (.leaf (-14)))) (.branch 42 (.leaf (-17)) (.branch 57 (.leaf (-18)) (.leaf (-21))))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-37))),
  (.branch 9 (.leaf (0)) (.branch 39 (.leaf (-7)) (.leaf (-13)))),
  (.branch 13 (.leaf (0)) (.leaf (-23))),
  (.branch 31 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 66 (.branch 62 (.leaf (-15)) (.leaf (-14))) (.branch 70 (.leaf (-13)) (.branch 71 (.leaf (-10)) (.leaf (-7))))),
  (.branch 69 (.branch 58 (.leaf (-21)) (.leaf (-20))) (.branch 70 (.leaf (-17)) (.branch 71 (.leaf (-14)) (.leaf (-11))))),
  (.branch 71 (.leaf (-2)) (.leaf (-1))),
  (.branch 63 (.leaf (-1)) (.leaf (0))),
  (.branch 67 (.branch 25 (.branch 4 (.leaf (-37)) (.leaf (-36))) (.branch 46 (.leaf (-35)) (.leaf (-34)))) (.branch 69 (.branch 68 (.leaf (-29)) (.leaf (-24))) (.branch 70 (.leaf (-19)) (.branch 71 (.leaf (-14)) (.leaf (-9)))))),
  (.branch 40 (.leaf (-13)) (.branch 61 (.leaf (-12)) (.leaf (-9)))),
  (.branch 60 (.branch 54 (.branch 51 (.branch 50 (.leaf (-23)) (.leaf (-22))) (.branch 52 (.leaf (-21)) (.branch 53 (.leaf (-20)) (.leaf (-19))))) (.branch 57 (.branch 55 (.leaf (-18)) (.branch 56 (.leaf (-17)) (.leaf (-16)))) (.branch 58 (.leaf (-15)) (.branch 59 (.leaf (-14)) (.leaf (-13)))))) (.branch 66 (.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-11)) (.leaf (-10)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7))))) (.branch 69 (.branch 67 (.leaf (-6)) (.branch 68 (.leaf (-5)) (.leaf (-4)))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 69 (.branch 68 (.leaf (-5)) (.leaf (-4))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_132_1055 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (4)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (6)) (.branch 26 (.leaf (0)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (3)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (4)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (3)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (2)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (5)) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (3)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (4)))) (.branch 51 (.branch 50 (.leaf (2)) (.leaf (1))) (.branch 52 (.leaf (0)) (.branch 53 (.leaf (2)) (.leaf (3))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (4)) (.leaf (2)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (7)) (.branch 62 (.leaf (0)) (.leaf (2)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (3)) (.leaf (1))) (.branch 66 (.leaf (0)) (.leaf (4)))) (.branch 69 (.branch 68 (.leaf (2)) (.leaf (1))) (.branch 70 (.leaf (0)) (.branch 71 (.leaf (2)) (.leaf (3)))))))))
  code := certificateD8_1055
  counts := ![(.branch 34 (.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))) (.branch 52 (.branch 41 (.branch 37 (.leaf (10)) (.leaf (11))) (.branch 44 (.leaf (12)) (.branch 48 (.leaf (13)) (.leaf (14))))) (.branch 62 (.branch 55 (.leaf (15)) (.branch 59 (.leaf (16)) (.leaf (17)))) (.branch 66 (.leaf (18)) (.branch 70 (.leaf (19)) (.leaf (20))))))),
  (.branch 33 (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 51 (.branch 42 (.branch 38 (.leaf (8)) (.leaf (9))) (.branch 47 (.leaf (10)) (.leaf (11)))) (.branch 60 (.branch 56 (.leaf (12)) (.leaf (13))) (.branch 65 (.leaf (14)) (.branch 69 (.leaf (15)) (.leaf (16))))))),
  (.branch 35 (.branch 17 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))) (.branch 53 (.branch 45 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 50 (.leaf (10)) (.leaf (11)))) (.branch 63 (.branch 58 (.leaf (12)) (.leaf (13))) (.branch 68 (.leaf (14)) (.branch 71 (.leaf (15)) (.leaf (16))))))),
  (.branch 36 (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 64 (.leaf (6)) (.branch 72 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 67 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 61 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 35 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-5)))) (.branch 53 (.leaf (-7)) (.branch 71 (.leaf (-9)) (.leaf (-11))))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-29))),
  (.branch 25 (.leaf (0)) (.leaf (-47))),
  (.branch 61 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 67 (.branch 63 (.leaf (-14)) (.leaf (-12))) (.branch 71 (.leaf (-10)) (.leaf (-5)))),
  (.branch 70 (.leaf (-6)) (.branch 71 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-11)),
  (.leaf (0)),
  (.branch 69 (.branch 58 (.leaf (-6)) (.branch 68 (.leaf (-5)) (.leaf (-4)))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1))))),
  (.branch 57 (.branch 50 (.branch 46 (.branch 44 (.leaf (-29)) (.branch 45 (.leaf (-28)) (.leaf (-27)))) (.branch 48 (.branch 47 (.leaf (-26)) (.leaf (-25))) (.branch 49 (.leaf (-24)) (.leaf (-23))))) (.branch 53 (.branch 51 (.leaf (-22)) (.branch 52 (.leaf (-21)) (.leaf (-20)))) (.branch 55 (.branch 54 (.leaf (-19)) (.leaf (-18))) (.branch 56 (.leaf (-17)) (.leaf (-16)))))) (.branch 64 (.branch 60 (.branch 58 (.leaf (-15)) (.branch 59 (.leaf (-14)) (.leaf (-13)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-11))) (.branch 63 (.leaf (-10)) (.leaf (-9))))) (.branch 68 (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-7))) (.branch 67 (.leaf (-6)) (.leaf (-5)))) (.branch 70 (.branch 69 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (-47)) (.leaf (-46))) (.branch 28 (.leaf (-45)) (.branch 29 (.leaf (-44)) (.leaf (-43))))) (.branch 33 (.branch 31 (.leaf (-42)) (.branch 32 (.leaf (-41)) (.leaf (-40)))) (.branch 34 (.leaf (-39)) (.branch 35 (.leaf (-38)) (.leaf (-37)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (-36)) (.branch 38 (.leaf (-35)) (.leaf (-34)))) (.branch 40 (.leaf (-33)) (.branch 41 (.leaf (-32)) (.leaf (-31))))) (.branch 45 (.branch 43 (.leaf (-30)) (.branch 44 (.leaf (-29)) (.leaf (-28)))) (.branch 46 (.leaf (-27)) (.branch 47 (.leaf (-26)) (.leaf (-25))))))) (.branch 60 (.branch 54 (.branch 51 (.branch 49 (.leaf (-24)) (.branch 50 (.leaf (-23)) (.leaf (-22)))) (.branch 52 (.leaf (-21)) (.branch 53 (.leaf (-20)) (.leaf (-19))))) (.branch 57 (.branch 55 (.leaf (-18)) (.branch 56 (.leaf (-17)) (.leaf (-16)))) (.branch 58 (.leaf (-15)) (.branch 59 (.leaf (-14)) (.leaf (-13)))))) (.branch 66 (.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-11)) (.leaf (-10)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7))))) (.branch 69 (.branch 67 (.leaf (-6)) (.branch 68 (.leaf (-5)) (.leaf (-4)))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 66 (.branch 63 (.branch 62 (.leaf (-11)) (.leaf (-10))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7))))) (.branch 69 (.branch 67 (.leaf (-6)) (.branch 68 (.leaf (-5)) (.leaf (-4)))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_132_1056 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (6)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (4)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (7))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (4)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (2)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (7))) (.branch 30 (.leaf (4)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (3)) (.leaf (6)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (2)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (3))) (.branch 43 (.leaf (5)) (.branch 44 (.leaf (7)) (.leaf (1)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (0)) (.leaf (2))) (.branch 48 (.leaf (4)) (.leaf (3)))) (.branch 51 (.branch 50 (.leaf (0)) (.leaf (6))) (.branch 52 (.leaf (5)) (.branch 53 (.leaf (1)) (.leaf (2))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (3))) (.branch 57 (.leaf (4)) (.leaf (7)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (5)) (.branch 62 (.leaf (2)) (.leaf (3)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (0)) (.leaf (6))) (.branch 66 (.leaf (4)) (.leaf (1)))) (.branch 69 (.branch 68 (.leaf (0)) (.leaf (2))) (.branch 70 (.leaf (5)) (.branch 71 (.leaf (3)) (.leaf (7)))))))))
  code := certificateD8_1056
  counts := ![(.branch 32 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 50 (.branch 41 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 59 (.branch 55 (.leaf (12)) (.leaf (13))) (.branch 64 (.leaf (14)) (.branch 68 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 38 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 60 (.leaf (8)) (.branch 67 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 40 (.leaf (5)) (.branch 47 (.leaf (6)) (.leaf (7)))) (.branch 62 (.leaf (8)) (.branch 69 (.leaf (9)) (.leaf (10)))))),
  (.branch 35 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 56 (.branch 42 (.leaf (5)) (.branch 49 (.leaf (6)) (.leaf (7)))) (.branch 63 (.leaf (8)) (.branch 71 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.branch 70 (.leaf (7)) (.leaf (8)))))),
  (.branch 36 (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 65 (.leaf (4)) (.leaf (5))))),
  (.branch 44 (.branch 15 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 58 (.leaf (3)) (.branch 72 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-26)) (.leaf (-27)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-16))) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-6))) (.branch 20 (.leaf (-7)) (.branch 27 (.leaf (-8)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (-32))) (.branch 36 (.leaf (-34)) (.leaf (-36)))),
  (.leaf (0))]
  high := ![(.branch 70 (.branch 69 (.leaf (-8)) (.leaf (-6))) (.branch 71 (.leaf (-4)) (.leaf (-2)))),
  (.branch 69 (.branch 46 (.leaf (-27)) (.branch 68 (.leaf (-25)) (.leaf (-20)))) (.branch 70 (.leaf (-15)) (.branch 71 (.leaf (-10)) (.leaf (-5))))),
  (.branch 70 (.branch 55 (.leaf (-18)) (.leaf (-15))) (.branch 71 (.leaf (-10)) (.leaf (-5)))),
  (.branch 64 (.leaf (-9)) (.leaf (-5))),
  (.branch 69 (.branch 67 (.leaf (-6)) (.branch 68 (.leaf (-5)) (.leaf (-4)))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1))))),
  (.branch 71 (.leaf (-2)) (.leaf (-1))),
  (.branch 68 (.branch 66 (.branch 37 (.leaf (-36)) (.leaf (-35))) (.branch 67 (.leaf (-30)) (.leaf (-25)))) (.branch 70 (.branch 69 (.leaf (-20)) (.leaf (-15))) (.branch 71 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0))]
def witnessD8_132_1057 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (7)) (.branch 8 (.leaf (1)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (6)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (6))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (5)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (7)) (.branch 26 (.leaf (1)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (2)) (.leaf (6)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (5)) (.leaf (2)))) (.branch 42 (.branch 41 (.leaf (3)) (.leaf (0))) (.branch 43 (.leaf (7)) (.branch 44 (.leaf (1)) (.leaf (4)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (2)) (.leaf (0))) (.branch 48 (.leaf (6)) (.leaf (1)))) (.branch 51 (.branch 50 (.leaf (5)) (.leaf (3))) (.branch 52 (.leaf (0)) (.branch 53 (.leaf (2)) (.leaf (6))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (4)) (.leaf (1))) (.branch 57 (.leaf (0)) (.leaf (2)))) (.branch 60 (.branch 59 (.leaf (3)) (.leaf (5))) (.branch 61 (.leaf (7)) (.branch 62 (.leaf (1)) (.leaf (0)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (2)) (.leaf (4))) (.branch 66 (.leaf (6)) (.leaf (1)))) (.branch 69 (.branch 68 (.leaf (0)) (.leaf (3))) (.branch 70 (.leaf (5)) (.branch 71 (.leaf (2)) (.leaf (6)))))))))
  code := certificateD8_1057
  counts := ![(.branch 32 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))) (.branch 52 (.branch 42 (.branch 37 (.leaf (7)) (.leaf (8))) (.branch 47 (.leaf (9)) (.leaf (10)))) (.branch 63 (.branch 57 (.leaf (11)) (.leaf (12))) (.branch 68 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 67 (.leaf (11)) (.leaf (12)))))),
  (.branch 35 (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 53 (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))) (.branch 64 (.branch 58 (.leaf (9)) (.leaf (10))) (.branch 71 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 69 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 55 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 65 (.leaf (6)) (.leaf (7))))),
  (.branch 39 (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 60 (.branch 50 (.leaf (4)) (.leaf (5))) (.branch 70 (.leaf (6)) (.leaf (7))))),
  (.branch 36 (.branch 18 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 48 (.leaf (4)) (.leaf (5))) (.branch 66 (.leaf (6)) (.branch 72 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (-29)) (.leaf (-30)))) (.branch 16 (.leaf (-31)) (.branch 21 (.leaf (-32)) (.leaf (-33))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-51))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (-9))) (.branch 29 (.leaf (-11)) (.branch 39 (.leaf (-13)) (.leaf (-15))))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (-4))) (.branch 54 (.leaf (-8)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 69 (.branch 58 (.leaf (-33)) (.leaf (-28))) (.branch 70 (.leaf (-21)) (.branch 71 (.leaf (-14)) (.leaf (-7))))),
  (.branch 69 (.branch 68 (.leaf (-5)) (.leaf (-4))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1))))),
  (.branch 65 (.leaf (-2)) (.leaf (-1))),
  (.branch 70 (.branch 60 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1)))),
  (.branch 67 (.branch 35 (.branch 4 (.leaf (-51)) (.leaf (-50))) (.branch 66 (.leaf (-49)) (.leaf (-42)))) (.branch 69 (.branch 68 (.leaf (-35)) (.leaf (-28))) (.branch 70 (.leaf (-21)) (.branch 71 (.leaf (-14)) (.leaf (-7)))))),
  (.branch 40 (.leaf (-15)) (.branch 71 (.leaf (-14)) (.leaf (-7)))),
  (.branch 68 (.branch 55 (.leaf (-12)) (.branch 67 (.leaf (-11)) (.leaf (-10)))) (.branch 70 (.branch 69 (.leaf (-9)) (.leaf (-8))) (.branch 71 (.leaf (-7)) (.leaf (-6))))),
  (.branch 66 (.branch 63 (.branch 62 (.leaf (-11)) (.leaf (-10))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7))))) (.branch 69 (.branch 67 (.leaf (-6)) (.branch 68 (.leaf (-5)) (.leaf (-4)))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_132_1058 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (4)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (5)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (4)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (7))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (1)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (5))) (.branch 30 (.leaf (4)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (6)) (.leaf (2)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (3)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (5))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (1)) (.leaf (3)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (0)) (.leaf (7))) (.branch 48 (.leaf (4)) (.leaf (2)))) (.branch 51 (.branch 50 (.leaf (1)) (.leaf (0))) (.branch 52 (.leaf (3)) (.branch 53 (.leaf (5)) (.leaf (2))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (4)) (.leaf (3)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (6))) (.branch 61 (.leaf (2)) (.branch 62 (.leaf (1)) (.leaf (3)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (0)) (.leaf (5))) (.branch 66 (.leaf (4)) (.leaf (2)))) (.branch 69 (.branch 68 (.leaf (1)) (.leaf (0))) (.branch 70 (.leaf (3)) (.branch 71 (.leaf (7)) (.leaf (2)))))))))
  code := certificateD8_1058
  counts := ![(.branch 33 (.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 51 (.branch 41 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 59 (.branch 55 (.leaf (12)) (.leaf (13))) (.branch 64 (.leaf (14)) (.branch 69 (.leaf (15)) (.leaf (16))))))),
  (.branch 32 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 36 (.branch 18 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))) (.branch 54 (.branch 43 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))) (.branch 67 (.branch 61 (.leaf (9)) (.leaf (10))) (.branch 72 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 16 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 52 (.branch 40 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 63 (.branch 58 (.leaf (9)) (.leaf (10))) (.branch 70 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 47 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 71 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-6)) (.leaf (-7)))),
  (.branch 11 (.leaf (0)) (.leaf (-13))),
  (.branch 47 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 65 (.branch 60 (.leaf (-8)) (.leaf (-7))) (.branch 70 (.leaf (-6)) (.branch 71 (.leaf (-4)) (.leaf (-2))))),
  (.branch 70 (.branch 69 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 64 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1)))),
  (.branch 69 (.branch 67 (.leaf (-6)) (.branch 68 (.leaf (-5)) (.leaf (-4)))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1))))),
  (.branch 68 (.branch 66 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5)))) (.branch 70 (.branch 69 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1))))),
  (.branch 65 (.branch 62 (.branch 36 (.leaf (-13)) (.branch 61 (.leaf (-12)) (.leaf (-11)))) (.branch 63 (.leaf (-10)) (.branch 64 (.leaf (-9)) (.leaf (-8))))) (.branch 68 (.branch 66 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5)))) (.branch 70 (.branch 69 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_132 : Fin 13 → CycleWitness 8 := ![witnessD8_132_1046, witnessD8_132_1047, witnessD8_132_1048, witnessD8_132_1049, witnessD8_132_1050, witnessD8_132_1051, witnessD8_132_1052, witnessD8_132_1053, witnessD8_132_1054, witnessD8_132_1055, witnessD8_132_1056, witnessD8_132_1057, witnessD8_132_1058]
end RealPinwheel.FiveSixths


