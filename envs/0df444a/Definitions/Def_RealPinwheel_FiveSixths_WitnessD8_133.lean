-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_133
-- name    : RealPinwheel_FiveSixths_WitnessD8_133
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:53:44.677531+00:00
-- url     : https://prove2.me/theorems/115dfef4-dcc0-4646-8284-6866a2abd3ac
-- title:
--   Exact witness block D8_133
-- statement:
--   These exact witnesses represent words 1060 through 1073 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1060–1073; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_133_1059 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (7)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (0)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (7)) (.leaf (0))) (.branch 30 (.leaf (5)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (0))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (6)) (.leaf (2)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (5)) (.leaf (0)))) (.branch 42 (.branch 41 (.leaf (3)) (.leaf (7))) (.branch 43 (.leaf (4)) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (5)) (.leaf (6)))) (.branch 51 (.branch 50 (.leaf (3)) (.leaf (0))) (.branch 52 (.leaf (4)) (.branch 53 (.leaf (1)) (.leaf (2))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (5))) (.branch 57 (.leaf (7)) (.leaf (0)))) (.branch 60 (.branch 59 (.leaf (3)) (.leaf (1))) (.branch 61 (.leaf (4)) (.branch 62 (.leaf (0)) (.leaf (2)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (6)) (.leaf (0))) (.branch 66 (.leaf (5)) (.leaf (1)))) (.branch 69 (.branch 68 (.leaf (3)) (.leaf (0))) (.branch 70 (.leaf (4)) (.branch 71 (.leaf (7)) (.leaf (2)))))))))
  code := certificateD8_1059
  counts := ![(.branch 33 (.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))) (.branch 51 (.branch 40 (.branch 37 (.leaf (10)) (.leaf (11))) (.branch 44 (.leaf (12)) (.branch 47 (.leaf (13)) (.leaf (14))))) (.branch 62 (.branch 55 (.leaf (15)) (.branch 58 (.leaf (16)) (.leaf (17)))) (.branch 65 (.leaf (18)) (.branch 69 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 38 (.leaf (5)) (.branch 46 (.leaf (6)) (.leaf (7)))) (.branch 60 (.leaf (8)) (.branch 67 (.leaf (9)) (.leaf (10)))))),
  (.branch 36 (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.branch 72 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.branch 70 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 42 (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 57 (.leaf (3)) (.branch 71 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.leaf (-26))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.branch 49 (.leaf (-42)) (.leaf (-43)))),
  (.branch 13 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 70 (.branch 66 (.leaf (-17)) (.leaf (-15))) (.branch 71 (.leaf (-10)) (.leaf (-5)))),
  (.branch 69 (.branch 39 (.leaf (-26)) (.branch 68 (.leaf (-25)) (.leaf (-20)))) (.branch 70 (.leaf (-15)) (.branch 71 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 70 (.branch 69 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1)))),
  (.branch 71 (.leaf (-2)) (.leaf (-1))),
  (.branch 68 (.branch 57 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5)))) (.branch 70 (.branch 69 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1))))),
  (.branch 67 (.branch 65 (.branch 50 (.leaf (-43)) (.leaf (-40))) (.branch 66 (.leaf (-35)) (.leaf (-30)))) (.branch 69 (.branch 68 (.leaf (-25)) (.leaf (-20))) (.branch 70 (.leaf (-15)) (.branch 71 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 14 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5))))]
def witnessD8_133_1060 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (6)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (7)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (6)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (1)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (6))) (.branch 30 (.leaf (4)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (1))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (7)) (.leaf (2)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (6)) (.leaf (3)))) (.branch 42 (.branch 41 (.leaf (4)) (.leaf (0))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (1)) (.leaf (5)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (3)) (.leaf (0))) (.branch 48 (.leaf (4)) (.leaf (6)))) (.branch 51 (.branch 50 (.leaf (2)) (.leaf (1))) (.branch 52 (.leaf (0)) (.branch 53 (.leaf (7)) (.leaf (3))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (5)) (.leaf (1))) (.branch 57 (.leaf (0)) (.leaf (2)))) (.branch 60 (.branch 59 (.leaf (4)) (.leaf (6))) (.branch 61 (.leaf (3)) (.branch 62 (.leaf (1)) (.leaf (0)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (2)) (.leaf (5))) (.branch 66 (.leaf (4)) (.leaf (0)))) (.branch 69 (.branch 68 (.leaf (3)) (.leaf (1))) (.branch 70 (.leaf (6)) (.branch 71 (.leaf (7)) (.leaf (2)))))))))
  code := certificateD8_1060
  counts := ![(.branch 31 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))) (.branch 52 (.branch 42 (.branch 37 (.leaf (7)) (.leaf (8))) (.branch 47 (.leaf (9)) (.leaf (10)))) (.branch 63 (.branch 57 (.leaf (11)) (.leaf (12))) (.branch 67 (.leaf (13)) (.leaf (14)))))),
  (.branch 33 (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 69 (.leaf (11)) (.leaf (12)))))),
  (.branch 36 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 58 (.branch 43 (.leaf (5)) (.branch 50 (.leaf (6)) (.leaf (7)))) (.branch 64 (.leaf (8)) (.branch 72 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 40 (.leaf (5)) (.branch 46 (.leaf (6)) (.leaf (7)))) (.branch 61 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 55 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 65 (.leaf (6)) (.leaf (7))))),
  (.branch 39 (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 60 (.branch 49 (.leaf (4)) (.leaf (5))) (.branch 70 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.branch 71 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 11 (.leaf (-26)) (.leaf (-27)))) (.branch 31 (.branch 21 (.leaf (-28)) (.leaf (-29))) (.branch 67 (.leaf (-31)) (.leaf (-32))))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 28 (.leaf (-2)) (.branch 64 (.leaf (-4)) (.leaf (-5))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 46 (.leaf (-18)) (.leaf (-19)))),
  (.branch 30 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-8)))) (.branch 48 (.leaf (-10)) (.branch 66 (.leaf (-12)) (.leaf (-14))))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-22)) (.leaf (-23)))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))) (.branch 39 (.leaf (-6)) (.branch 49 (.leaf (-7)) (.leaf (-8))))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 69 (.branch 68 (.leaf (-32)) (.leaf (-26))) (.branch 70 (.leaf (-20)) (.branch 71 (.leaf (-14)) (.leaf (-8))))),
  (.branch 70 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1)))),
  (.branch 65 (.leaf (-5)) (.branch 66 (.leaf (-1)) (.leaf (0)))),
  (.branch 69 (.branch 47 (.leaf (-19)) (.leaf (-18))) (.branch 70 (.leaf (-14)) (.branch 71 (.leaf (-10)) (.leaf (-6))))),
  (.branch 69 (.branch 67 (.leaf (-14)) (.branch 68 (.leaf (-13)) (.leaf (-12)))) (.branch 70 (.leaf (-11)) (.branch 71 (.leaf (-10)) (.leaf (-9))))),
  (.branch 68 (.branch 66 (.branch 14 (.leaf (-23)) (.leaf (-22))) (.branch 67 (.leaf (-19)) (.leaf (-16)))) (.branch 70 (.branch 69 (.leaf (-13)) (.leaf (-10))) (.branch 71 (.leaf (-7)) (.leaf (-4))))),
  (.branch 50 (.leaf (-8)) (.branch 71 (.leaf (-7)) (.leaf (-4)))),
  (.leaf (-1))]
def witnessD8_133_1061 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (7)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (1)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (2)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (4)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (7)) (.leaf (1)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (1)) (.leaf (3)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (5))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (2)) (.leaf (0)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (6)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (3)))) (.branch 51 (.branch 50 (.leaf (2)) (.leaf (1))) (.branch 52 (.leaf (0)) (.branch 53 (.leaf (4)) (.leaf (1))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (2))) (.branch 57 (.leaf (1)) (.leaf (3)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (7))) (.branch 61 (.leaf (1)) (.branch 62 (.leaf (2)) (.leaf (0)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (5)) (.leaf (1))) (.branch 66 (.leaf (0)) (.leaf (3)))) (.branch 69 (.branch 68 (.leaf (2)) (.leaf (1))) (.branch 70 (.leaf (0)) (.branch 71 (.leaf (6)) (.leaf (1)))))))))
  code := certificateD8_1061
  counts := ![(.branch 34 (.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))) (.branch 52 (.branch 41 (.branch 37 (.leaf (10)) (.leaf (11))) (.branch 45 (.leaf (12)) (.branch 48 (.leaf (13)) (.leaf (14))))) (.branch 63 (.branch 55 (.leaf (15)) (.branch 59 (.leaf (16)) (.leaf (17)))) (.branch 66 (.leaf (18)) (.branch 70 (.leaf (19)) (.leaf (20))))))),
  (.branch 36 (.branch 18 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 33 (.leaf (8)) (.leaf (9)))))) (.branch 54 (.branch 43 (.branch 39 (.leaf (10)) (.leaf (11))) (.branch 47 (.leaf (12)) (.branch 51 (.leaf (13)) (.leaf (14))))) (.branch 65 (.branch 57 (.leaf (15)) (.branch 61 (.leaf (16)) (.leaf (17)))) (.branch 69 (.leaf (18)) (.branch 72 (.leaf (19)) (.leaf (20))))))),
  (.branch 32 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 67 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3)))),
  (.branch 46 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 71 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 39 (.leaf (-3)) (.branch 57 (.leaf (-4)) (.leaf (-5))))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.branch 28 (.leaf (-37)) (.leaf (-42)))),
  (.branch 17 (.leaf (0)) (.branch 64 (.leaf (-15)) (.leaf (-19)))),
  (.branch 24 (.leaf (0)) (.branch 46 (.leaf (-1)) (.leaf (-6)))),
  (.branch 10 (.leaf (0)) (.leaf (-29)))]
  high := ![(.branch 67 (.branch 56 (.leaf (-13)) (.leaf (-12))) (.branch 71 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.branch 58 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 70 (.leaf (-2)) (.leaf (0))))),
  (.branch 70 (.branch 69 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1)))),
  (.branch 69 (.branch 68 (.leaf (-5)) (.leaf (-4))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1))))),
  (.branch 62 (.branch 57 (.branch 54 (.branch 29 (.leaf (-42)) (.leaf (-41))) (.branch 55 (.leaf (-39)) (.branch 56 (.leaf (-37)) (.leaf (-35))))) (.branch 59 (.branch 58 (.leaf (-33)) (.leaf (-31))) (.branch 60 (.leaf (-29)) (.branch 61 (.leaf (-27)) (.leaf (-25)))))) (.branch 67 (.branch 64 (.branch 63 (.leaf (-23)) (.leaf (-21))) (.branch 65 (.leaf (-19)) (.branch 66 (.leaf (-17)) (.leaf (-15))))) (.branch 69 (.branch 68 (.leaf (-13)) (.leaf (-11))) (.branch 70 (.leaf (-9)) (.branch 71 (.leaf (-7)) (.leaf (-5))))))),
  (.branch 68 (.branch 66 (.branch 65 (.leaf (-19)) (.leaf (-17))) (.branch 67 (.leaf (-15)) (.leaf (-13)))) (.branch 70 (.branch 69 (.leaf (-11)) (.leaf (-9))) (.branch 71 (.leaf (-7)) (.leaf (-5))))),
  (.branch 47 (.leaf (-6)) (.leaf (-5))),
  (.branch 65 (.branch 61 (.branch 11 (.leaf (-29)) (.branch 36 (.leaf (-28)) (.leaf (-27)))) (.branch 63 (.branch 62 (.leaf (-25)) (.leaf (-23))) (.branch 64 (.leaf (-21)) (.leaf (-19))))) (.branch 68 (.branch 66 (.leaf (-17)) (.branch 67 (.leaf (-15)) (.leaf (-13)))) (.branch 70 (.branch 69 (.leaf (-11)) (.leaf (-9))) (.branch 71 (.leaf (-7)) (.leaf (-5))))))]
def witnessD8_133_1062 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (0))) (.branch 16 (.leaf (7)) (.branch 17 (.leaf (1)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (4)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (6)) (.leaf (0))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (2)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (5))) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (0))) (.branch 34 (.leaf (7)) (.branch 35 (.leaf (1)) (.leaf (4)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (3)) (.leaf (1)))) (.branch 42 (.branch 41 (.leaf (6)) (.leaf (0))) (.branch 43 (.leaf (5)) (.branch 44 (.leaf (2)) (.leaf (1)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (0)) (.leaf (3))) (.branch 48 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 50 (.leaf (4)) (.leaf (0))) (.branch 52 (.leaf (7)) (.branch 53 (.leaf (1)) (.leaf (3))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (2))) (.branch 57 (.leaf (5)) (.leaf (1)))) (.branch 60 (.branch 59 (.leaf (6)) (.leaf (0))) (.branch 61 (.leaf (3)) (.branch 62 (.leaf (2)) (.leaf (1)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (0)) (.leaf (4))) (.branch 66 (.leaf (1)) (.leaf (2)))) (.branch 69 (.branch 68 (.leaf (3)) (.leaf (0))) (.branch 70 (.leaf (7)) (.branch 71 (.leaf (1)) (.leaf (5)))))))))
  code := certificateD8_1062
  counts := ![(.branch 33 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 51 (.branch 42 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 60 (.branch 55 (.leaf (12)) (.leaf (13))) (.branch 64 (.leaf (14)) (.branch 69 (.leaf (15)) (.leaf (16))))))),
  (.branch 35 (.branch 17 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))) (.branch 53 (.branch 45 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 48 (.leaf (10)) (.leaf (11)))) (.branch 63 (.branch 58 (.leaf (12)) (.leaf (13))) (.branch 66 (.leaf (14)) (.branch 71 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 67 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 39 (.leaf (5)) (.branch 47 (.leaf (6)) (.leaf (7)))) (.branch 61 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 36 (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 65 (.leaf (4)) (.leaf (5))))),
  (.branch 43 (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 57 (.leaf (3)) (.branch 72 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.branch 70 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 30 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-6)))) (.branch 48 (.leaf (-8)) (.branch 66 (.leaf (-10)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-21))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (-37)) (.leaf (-39)))),
  (.branch 14 (.leaf (0)) (.branch 57 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 70 (.branch 65 (.leaf (-7)) (.leaf (-6))) (.branch 71 (.leaf (-4)) (.leaf (-2)))),
  (.branch 67 (.leaf (-12)) (.leaf (-11))),
  (.branch 69 (.branch 68 (.leaf (-5)) (.leaf (-4))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1))))),
  (.branch 69 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 70 (.leaf (-15)) (.branch 71 (.leaf (-10)) (.leaf (-5))))),
  (.branch 67 (.branch 51 (.branch 22 (.leaf (-39)) (.leaf (-38))) (.branch 66 (.leaf (-35)) (.leaf (-30)))) (.branch 69 (.branch 68 (.leaf (-25)) (.leaf (-20))) (.branch 70 (.leaf (-15)) (.branch 71 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 58 (.leaf (-3)) (.leaf (0))),
  (.branch 65 (.branch 62 (.branch 60 (.leaf (-13)) (.branch 61 (.leaf (-12)) (.leaf (-11)))) (.branch 63 (.leaf (-10)) (.branch 64 (.leaf (-9)) (.leaf (-8))))) (.branch 68 (.branch 66 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5)))) (.branch 70 (.branch 69 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 71 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_133_1063 : CycleWitness 8 where
  length := 72
  word := (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (4)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (7)) (.branch 17 (.leaf (1)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (5)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (2)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (6)) (.leaf (1))) (.branch 30 (.leaf (4)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (7)) (.branch 35 (.leaf (1)) (.leaf (5)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (3)) (.leaf (4)))) (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (6)) (.branch 44 (.leaf (2)) (.leaf (0)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (3)) (.leaf (1))) (.branch 48 (.leaf (4)) (.leaf (5)))) (.branch 51 (.branch 50 (.leaf (0)) (.leaf (2))) (.branch 52 (.leaf (7)) (.branch 53 (.leaf (1)) (.leaf (3))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (2))) (.branch 57 (.leaf (6)) (.leaf (4)))) (.branch 60 (.branch 59 (.leaf (1)) (.leaf (0))) (.branch 61 (.leaf (3)) (.branch 62 (.leaf (2)) (.leaf (0)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (5)) (.leaf (1))) (.branch 66 (.leaf (4)) (.leaf (3)))) (.branch 69 (.branch 68 (.leaf (0)) (.leaf (2))) (.branch 70 (.leaf (7)) (.branch 71 (.leaf (1)) (.leaf (6)))))))))
  code := certificateD8_1063
  counts := ![(.branch 32 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 50 (.branch 42 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 45 (.leaf (10)) (.leaf (11)))) (.branch 60 (.branch 55 (.leaf (12)) (.leaf (13))) (.branch 63 (.leaf (14)) (.branch 68 (.leaf (15)) (.leaf (16))))))),
  (.branch 35 (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))) (.branch 53 (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))) (.branch 65 (.branch 59 (.leaf (9)) (.leaf (10))) (.branch 71 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 69 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 39 (.leaf (5)) (.branch 46 (.leaf (6)) (.leaf (7)))) (.branch 61 (.leaf (8)) (.branch 67 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 36 (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 43 (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 57 (.leaf (3)) (.branch 72 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.branch 70 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 27 (.branch 1 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-15)))) (.branch 45 (.leaf (-17)) (.branch 63 (.leaf (-19)) (.leaf (-21))))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 31 (.leaf (-14)) (.branch 67 (.leaf (-17)) (.leaf (-19))))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (-15))) (.branch 49 (.leaf (-16)) (.leaf (-18)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 69 (.branch 64 (.leaf (-21)) (.leaf (-20))) (.branch 70 (.leaf (-17)) (.branch 71 (.leaf (-14)) (.leaf (-11))))),
  (.leaf (-1)),
  (.branch 70 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 71 (.leaf (-2)) (.leaf (-1)))),
  (.branch 69 (.branch 68 (.leaf (-19)) (.leaf (-16))) (.branch 70 (.leaf (-13)) (.branch 71 (.leaf (-10)) (.leaf (-7))))),
  (.branch 69 (.branch 67 (.leaf (-6)) (.branch 68 (.leaf (-5)) (.leaf (-4)))) (.branch 70 (.leaf (-3)) (.branch 71 (.leaf (-2)) (.leaf (-1))))),
  (.branch 67 (.branch 65 (.branch 50 (.leaf (-18)) (.leaf (-17))) (.branch 66 (.leaf (-15)) (.leaf (-13)))) (.branch 69 (.branch 68 (.leaf (-11)) (.leaf (-9))) (.branch 70 (.leaf (-7)) (.branch 71 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 14 (.leaf (-3)) (.branch 58 (.leaf (-2)) (.leaf (0)))),
  (.branch 71 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_133_1064 : CycleWitness 8 where
  length := 71
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (7))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (6))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (5))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (7)) (.leaf (0))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (1)) (.leaf (0)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (4)) (.leaf (6)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (5))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (1)) (.leaf (0)))))))) (.branch 53 (.branch 44 (.branch 39 (.branch 37 (.branch 36 (.leaf (3)) (.leaf (1))) (.branch 38 (.leaf (7)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (4))) (.branch 42 (.leaf (6)) (.branch 43 (.leaf (1)) (.leaf (0)))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (2)) (.leaf (1))) (.branch 47 (.leaf (5)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (7))) (.branch 51 (.leaf (2)) (.branch 52 (.leaf (1)) (.leaf (0))))))) (.branch 62 (.branch 57 (.branch 55 (.branch 54 (.leaf (4)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (6)))) (.branch 59 (.branch 58 (.leaf (0)) (.leaf (3))) (.branch 60 (.leaf (1)) (.branch 61 (.leaf (5)) (.leaf (2)))))) (.branch 66 (.branch 64 (.branch 63 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (7)) (.leaf (4)))) (.branch 68 (.branch 67 (.leaf (0)) (.leaf (2))) (.branch 69 (.leaf (1)) (.branch 70 (.leaf (6)) (.leaf (3)))))))))
  code := certificateD8_1064
  counts := ![(.branch 31 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 49 (.branch 40 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 58 (.branch 53 (.leaf (12)) (.leaf (13))) (.branch 63 (.leaf (14)) (.branch 67 (.leaf (15)) (.leaf (16))))))),
  (.branch 34 (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 52 (.branch 43 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 60 (.branch 55 (.leaf (12)) (.leaf (13))) (.branch 64 (.leaf (14)) (.branch 69 (.leaf (15)) (.leaf (16))))))),
  (.branch 33 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 36 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 59 (.branch 48 (.leaf (3)) (.leaf (4))) (.branch 71 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 61 (.leaf (4)) (.leaf (5))))),
  (.branch 42 (.branch 14 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 57 (.leaf (3)) (.branch 70 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 6 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 65 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 13 (.leaf (-8)) (.branch 26 (.leaf (-10)) (.leaf (-11))))),
  (.branch 28 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-4)) (.leaf (-6)))) (.branch 46 (.branch 37 (.leaf (-7)) (.leaf (-8))) (.branch 55 (.leaf (-9)) (.branch 64 (.leaf (-10)) (.leaf (-11)))))),
  (.branch 3 (.leaf (0)) (.branch 56 (.leaf (-35)) (.leaf (-38)))),
  (.branch 59 (.leaf (0)) (.leaf (-1))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (-13))) (.branch 29 (.leaf (-14)) (.branch 41 (.leaf (-24)) (.leaf (-25))))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-21)) (.leaf (-24)))),
  (.branch 42 (.branch 14 (.leaf (0)) (.leaf (-1))) (.branch 70 (.leaf (-3)) (.leaf (-5)))),
  (.branch 50 (.branch 6 (.leaf (0)) (.leaf (-19))) (.branch 65 (.leaf (-24)) (.leaf (-25))))]
  high := ![(.branch 68 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 69 (.leaf (-8)) (.branch 70 (.leaf (-6)) (.leaf (-4))))),
  (.branch 70 (.leaf (-11)) (.leaf (-10))),
  (.branch 63 (.branch 57 (.leaf (-38)) (.leaf (-37))) (.branch 69 (.leaf (-36)) (.branch 70 (.leaf (-24)) (.leaf (-12))))),
  (.branch 60 (.leaf (-1)) (.leaf (0))),
  (.branch 68 (.branch 42 (.leaf (-25)) (.branch 67 (.leaf (-24)) (.leaf (-21)))) (.branch 69 (.leaf (-18)) (.branch 70 (.leaf (-15)) (.leaf (-12))))),
  (.branch 65 (.branch 62 (.branch 18 (.leaf (-24)) (.leaf (-23))) (.branch 63 (.leaf (-21)) (.branch 64 (.leaf (-19)) (.leaf (-17))))) (.branch 68 (.branch 66 (.leaf (-15)) (.branch 67 (.leaf (-13)) (.leaf (-11)))) (.branch 69 (.leaf (-9)) (.branch 70 (.leaf (-7)) (.leaf (-5)))))),
  (.leaf (-5)),
  (.branch 68 (.branch 66 (.leaf (-25)) (.branch 67 (.leaf (-23)) (.leaf (-21)))) (.branch 69 (.leaf (-19)) (.branch 70 (.leaf (-17)) (.leaf (-15)))))]
def witnessD8_133_1065 : CycleWitness 8 where
  length := 70
  word := (.branch 36 (.branch 17 (.branch 9 (.branch 5 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (1)))))) (.branch 25 (.branch 22 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.leaf (1)) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 30 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (4)) (.leaf (0)))) (.branch 33 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (2)) (.leaf (0))))))) (.branch 52 (.branch 44 (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (5)) (.leaf (0))))) (.branch 48 (.branch 45 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (2)))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (0)))))) (.branch 61 (.branch 56 (.branch 53 (.leaf (2)) (.branch 55 (.leaf (0)) (.leaf (6)))) (.branch 58 (.leaf (0)) (.branch 59 (.leaf (1)) (.leaf (0))))) (.branch 65 (.branch 62 (.leaf (2)) (.branch 64 (.leaf (0)) (.leaf (1)))) (.branch 67 (.branch 66 (.leaf (0)) (.leaf (2))) (.branch 69 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_1065
  counts := ![(.branch 35 (.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 8 (.leaf (5)) (.branch 10 (.leaf (6)) (.leaf (7)))) (.branch 13 (.leaf (8)) (.branch 15 (.leaf (9)) (.leaf (10)))))) (.branch 26 (.branch 21 (.branch 18 (.leaf (11)) (.branch 19 (.leaf (12)) (.leaf (13)))) (.branch 22 (.leaf (14)) (.branch 24 (.leaf (15)) (.leaf (16))))) (.branch 30 (.branch 27 (.leaf (17)) (.branch 29 (.leaf (18)) (.leaf (19)))) (.branch 32 (.leaf (20)) (.branch 33 (.leaf (21)) (.leaf (22))))))) (.branch 52 (.branch 43 (.branch 38 (.branch 36 (.leaf (23)) (.leaf (24))) (.branch 40 (.leaf (25)) (.branch 41 (.leaf (26)) (.leaf (27))))) (.branch 47 (.branch 44 (.leaf (28)) (.branch 46 (.leaf (29)) (.leaf (30)))) (.branch 49 (.leaf (31)) (.branch 50 (.leaf (32)) (.leaf (33)))))) (.branch 61 (.branch 57 (.branch 54 (.leaf (34)) (.branch 55 (.leaf (35)) (.leaf (36)))) (.branch 58 (.leaf (37)) (.branch 60 (.leaf (38)) (.leaf (39))))) (.branch 66 (.branch 63 (.leaf (40)) (.branch 64 (.leaf (41)) (.leaf (42)))) (.branch 68 (.leaf (43)) (.branch 69 (.leaf (44)) (.leaf (45)))))))),
  (.branch 31 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 65 (.leaf (9)) (.leaf (10)))))),
  (.branch 34 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 39 (.leaf (5)) (.branch 48 (.leaf (6)) (.leaf (7)))) (.branch 62 (.leaf (8)) (.branch 67 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1))),
  (.branch 70 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-10)) (.branch 8 (.leaf (-11)) (.leaf (-12))))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 25 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (-2)) (.leaf (-5)))) (.branch 53 (.branch 39 (.leaf (-7)) (.leaf (-9))) (.branch 67 (.leaf (-11)) (.leaf (-13))))),
  (.branch 14 (.leaf (0)) (.leaf (-56))),
  (.branch 28 (.leaf (0)) (.leaf (-42))),
  (.branch 42 (.leaf (0)) (.leaf (-28))),
  (.branch 56 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 65 (.leaf (-12)) (.leaf (-9))),
  (.branch 67 (.branch 66 (.leaf (-5)) (.leaf (-4))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.branch 68 (.leaf (-13)) (.branch 69 (.leaf (-12)) (.leaf (-11)))),
  (.branch 42 (.branch 28 (.branch 21 (.branch 17 (.branch 15 (.leaf (-56)) (.branch 16 (.leaf (-55)) (.leaf (-54)))) (.branch 19 (.branch 18 (.leaf (-53)) (.leaf (-52))) (.branch 20 (.leaf (-51)) (.leaf (-50))))) (.branch 24 (.branch 22 (.leaf (-49)) (.branch 23 (.leaf (-48)) (.leaf (-47)))) (.branch 26 (.branch 25 (.leaf (-46)) (.leaf (-45))) (.branch 27 (.leaf (-44)) (.leaf (-43)))))) (.branch 35 (.branch 31 (.branch 29 (.leaf (-42)) (.branch 30 (.leaf (-41)) (.leaf (-40)))) (.branch 33 (.branch 32 (.leaf (-39)) (.leaf (-38))) (.branch 34 (.leaf (-37)) (.leaf (-36))))) (.branch 38 (.branch 36 (.leaf (-35)) (.branch 37 (.leaf (-34)) (.leaf (-33)))) (.branch 40 (.branch 39 (.leaf (-32)) (.leaf (-31))) (.branch 41 (.leaf (-30)) (.leaf (-29))))))) (.branch 56 (.branch 49 (.branch 45 (.branch 43 (.leaf (-28)) (.branch 44 (.leaf (-27)) (.leaf (-26)))) (.branch 47 (.branch 46 (.leaf (-25)) (.leaf (-24))) (.branch 48 (.leaf (-23)) (.leaf (-22))))) (.branch 52 (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-20)) (.leaf (-19)))) (.branch 54 (.branch 53 (.leaf (-18)) (.leaf (-17))) (.branch 55 (.leaf (-16)) (.leaf (-15)))))) (.branch 63 (.branch 59 (.branch 57 (.leaf (-14)) (.branch 58 (.leaf (-13)) (.leaf (-12)))) (.branch 61 (.branch 60 (.leaf (-11)) (.leaf (-10))) (.branch 62 (.leaf (-9)) (.leaf (-8))))) (.branch 66 (.branch 64 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 38 (.branch 33 (.branch 30 (.branch 29 (.leaf (-42)) (.leaf (-41))) (.branch 31 (.leaf (-40)) (.branch 32 (.leaf (-39)) (.leaf (-38))))) (.branch 35 (.branch 34 (.leaf (-37)) (.leaf (-36))) (.branch 36 (.leaf (-35)) (.branch 37 (.leaf (-34)) (.leaf (-33)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-32)) (.leaf (-31))) (.branch 41 (.leaf (-30)) (.branch 42 (.leaf (-29)) (.leaf (-28))))) (.branch 46 (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-26)) (.leaf (-25)))) (.branch 47 (.leaf (-24)) (.branch 48 (.leaf (-23)) (.leaf (-22))))))) (.branch 59 (.branch 54 (.branch 51 (.branch 50 (.leaf (-21)) (.leaf (-20))) (.branch 52 (.leaf (-19)) (.branch 53 (.leaf (-18)) (.leaf (-17))))) (.branch 56 (.branch 55 (.leaf (-16)) (.leaf (-15))) (.branch 57 (.leaf (-14)) (.branch 58 (.leaf (-13)) (.leaf (-12)))))) (.branch 64 (.branch 61 (.branch 60 (.leaf (-11)) (.leaf (-10))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-8)) (.leaf (-7))))) (.branch 67 (.branch 65 (.leaf (-6)) (.branch 66 (.leaf (-5)) (.leaf (-4)))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 56 (.branch 49 (.branch 45 (.branch 43 (.leaf (-28)) (.branch 44 (.leaf (-27)) (.leaf (-26)))) (.branch 47 (.branch 46 (.leaf (-25)) (.leaf (-24))) (.branch 48 (.leaf (-23)) (.leaf (-22))))) (.branch 52 (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-20)) (.leaf (-19)))) (.branch 54 (.branch 53 (.leaf (-18)) (.leaf (-17))) (.branch 55 (.leaf (-16)) (.leaf (-15)))))) (.branch 63 (.branch 59 (.branch 57 (.leaf (-14)) (.branch 58 (.leaf (-13)) (.leaf (-12)))) (.branch 61 (.branch 60 (.leaf (-11)) (.leaf (-10))) (.branch 62 (.leaf (-9)) (.leaf (-8))))) (.branch 66 (.branch 64 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.branch 59 (.branch 57 (.leaf (-14)) (.branch 58 (.leaf (-13)) (.leaf (-12)))) (.branch 61 (.branch 60 (.leaf (-11)) (.leaf (-10))) (.branch 62 (.leaf (-9)) (.leaf (-8))))) (.branch 66 (.branch 64 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_133_1066 : CycleWitness 8 where
  length := 70
  word := (.branch 35 (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 16 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (1)) (.leaf (0)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (1))))) (.branch 31 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (0)) (.leaf (1))))))) (.branch 52 (.branch 44 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (0)) (.leaf (5)))) (.branch 41 (.branch 40 (.leaf (1)) (.leaf (0))) (.branch 42 (.leaf (2)) (.leaf (0))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (0)))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (6)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 59 (.branch 58 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (0)) (.leaf (2))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (0)) (.leaf (2)))) (.branch 67 (.branch 66 (.leaf (0)) (.leaf (7))) (.branch 68 (.leaf (1)) (.branch 69 (.leaf (0)) (.leaf (2)))))))))
  code := certificateD8_1066
  counts := ![(.branch 34 (.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 22 (.leaf (11)) (.leaf (12)))) (.branch 29 (.branch 27 (.leaf (13)) (.leaf (14))) (.branch 30 (.leaf (15)) (.branch 32 (.leaf (16)) (.leaf (17))))))) (.branch 52 (.branch 43 (.branch 38 (.branch 36 (.leaf (18)) (.leaf (19))) (.branch 41 (.leaf (20)) (.leaf (21)))) (.branch 46 (.branch 44 (.leaf (22)) (.leaf (23))) (.branch 48 (.leaf (24)) (.branch 50 (.leaf (25)) (.leaf (26)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (27)) (.leaf (28))) (.branch 58 (.leaf (29)) (.leaf (30)))) (.branch 64 (.branch 62 (.leaf (31)) (.leaf (32))) (.branch 66 (.leaf (33)) (.branch 69 (.leaf (34)) (.leaf (35)))))))),
  (.branch 35 (.branch 17 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))) (.branch 54 (.branch 45 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 49 (.leaf (10)) (.leaf (11)))) (.branch 63 (.branch 59 (.leaf (12)) (.leaf (13))) (.branch 68 (.leaf (14)) (.leaf (15)))))),
  (.branch 37 (.branch 19 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))) (.branch 56 (.branch 47 (.branch 42 (.leaf (8)) (.leaf (9))) (.branch 51 (.leaf (10)) (.leaf (11)))) (.branch 65 (.branch 61 (.leaf (12)) (.leaf (13))) (.branch 70 (.leaf (14)) (.leaf (15)))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 53 (.leaf (0)) (.leaf (1))),
  (.branch 67 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-5)) (.leaf (-7)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-59))),
  (.branch 25 (.leaf (0)) (.leaf (-45))),
  (.branch 39 (.leaf (0)) (.leaf (-31))),
  (.branch 53 (.leaf (0)) (.leaf (-17))),
  (.branch 67 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 67 (.leaf (-2)) (.leaf (-1))),
  (.branch 64 (.leaf (-7)) (.branch 69 (.leaf (-6)) (.leaf (-3)))),
  (.branch 66 (.leaf (-1)) (.leaf (0))),
  (.branch 40 (.branch 25 (.branch 18 (.branch 14 (.branch 12 (.leaf (-59)) (.branch 13 (.leaf (-58)) (.leaf (-57)))) (.branch 16 (.branch 15 (.leaf (-56)) (.leaf (-55))) (.branch 17 (.leaf (-54)) (.leaf (-53))))) (.branch 21 (.branch 19 (.leaf (-52)) (.branch 20 (.leaf (-51)) (.leaf (-50)))) (.branch 23 (.branch 22 (.leaf (-49)) (.leaf (-48))) (.branch 24 (.leaf (-47)) (.leaf (-46)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-45)) (.branch 27 (.leaf (-44)) (.leaf (-43)))) (.branch 30 (.branch 29 (.leaf (-42)) (.leaf (-41))) (.branch 31 (.leaf (-40)) (.leaf (-39))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-38)) (.leaf (-37))) (.branch 35 (.leaf (-36)) (.leaf (-35)))) (.branch 38 (.branch 37 (.leaf (-34)) (.leaf (-33))) (.branch 39 (.leaf (-32)) (.leaf (-31))))))) (.branch 55 (.branch 47 (.branch 43 (.branch 41 (.leaf (-30)) (.branch 42 (.leaf (-29)) (.leaf (-28)))) (.branch 45 (.branch 44 (.leaf (-27)) (.leaf (-26))) (.branch 46 (.leaf (-25)) (.leaf (-24))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-23)) (.leaf (-22))) (.branch 50 (.leaf (-21)) (.leaf (-20)))) (.branch 53 (.branch 52 (.leaf (-19)) (.leaf (-18))) (.branch 54 (.leaf (-17)) (.leaf (-16)))))) (.branch 62 (.branch 58 (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-14)) (.leaf (-13)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-11))) (.branch 61 (.leaf (-10)) (.leaf (-9))))) (.branch 66 (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (-45)) (.leaf (-44))) (.branch 28 (.leaf (-43)) (.branch 29 (.leaf (-42)) (.leaf (-41))))) (.branch 33 (.branch 31 (.leaf (-40)) (.branch 32 (.leaf (-39)) (.leaf (-38)))) (.branch 34 (.leaf (-37)) (.branch 35 (.leaf (-36)) (.leaf (-35)))))) (.branch 41 (.branch 38 (.branch 37 (.leaf (-34)) (.leaf (-33))) (.branch 39 (.leaf (-32)) (.branch 40 (.leaf (-31)) (.leaf (-30))))) (.branch 44 (.branch 42 (.leaf (-29)) (.branch 43 (.leaf (-28)) (.leaf (-27)))) (.branch 45 (.leaf (-26)) (.branch 46 (.leaf (-25)) (.leaf (-24))))))) (.branch 58 (.branch 52 (.branch 49 (.branch 48 (.leaf (-23)) (.leaf (-22))) (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-20)) (.leaf (-19))))) (.branch 55 (.branch 53 (.leaf (-18)) (.branch 54 (.leaf (-17)) (.leaf (-16)))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-14)) (.leaf (-13)))))) (.branch 64 (.branch 61 (.branch 59 (.leaf (-12)) (.branch 60 (.leaf (-11)) (.leaf (-10)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-8)) (.leaf (-7))))) (.branch 67 (.branch 65 (.leaf (-6)) (.branch 66 (.leaf (-5)) (.leaf (-4)))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 54 (.branch 46 (.branch 42 (.branch 40 (.leaf (-31)) (.branch 41 (.leaf (-30)) (.leaf (-29)))) (.branch 44 (.branch 43 (.leaf (-28)) (.leaf (-27))) (.branch 45 (.leaf (-26)) (.leaf (-25))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-24)) (.leaf (-23))) (.branch 49 (.leaf (-22)) (.leaf (-21)))) (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-19))) (.branch 53 (.leaf (-18)) (.leaf (-17)))))) (.branch 62 (.branch 58 (.branch 56 (.branch 55 (.leaf (-16)) (.leaf (-15))) (.branch 57 (.leaf (-14)) (.leaf (-13)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-11))) (.branch 61 (.leaf (-10)) (.leaf (-9))))) (.branch 66 (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 61 (.branch 57 (.branch 55 (.branch 54 (.leaf (-17)) (.leaf (-16))) (.branch 56 (.leaf (-15)) (.leaf (-14)))) (.branch 59 (.branch 58 (.leaf (-13)) (.leaf (-12))) (.branch 60 (.leaf (-11)) (.leaf (-10))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-7)) (.leaf (-6)))) (.branch 67 (.branch 66 (.leaf (-5)) (.leaf (-4))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_133_1067 : CycleWitness 8 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (6)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (7))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (3)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (0)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (7))) (.branch 29 (.leaf (0)) (.leaf (3)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (4))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (5)) (.leaf (6)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (3))) (.branch 42 (.leaf (7)) (.leaf (0))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (4)) (.leaf (0))) (.branch 46 (.leaf (5)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (6))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (2)) (.leaf (0))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (7)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (5))) (.branch 59 (.leaf (0)) (.branch 60 (.leaf (1)) (.leaf (0)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (2)) (.leaf (6))) (.branch 64 (.leaf (0)) (.leaf (3)))) (.branch 67 (.branch 66 (.leaf (0)) (.leaf (4))) (.branch 68 (.leaf (0)) (.branch 69 (.leaf (5)) (.leaf (7)))))))))
  code := certificateD8_1067
  counts := ![(.branch 33 (.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 29 (.branch 26 (.leaf (11)) (.leaf (12))) (.branch 31 (.leaf (13)) (.leaf (14)))))) (.branch 52 (.branch 43 (.branch 38 (.branch 36 (.leaf (15)) (.leaf (16))) (.branch 40 (.leaf (17)) (.leaf (18)))) (.branch 47 (.branch 45 (.leaf (19)) (.leaf (20))) (.branch 50 (.leaf (21)) (.leaf (22))))) (.branch 61 (.branch 57 (.branch 54 (.leaf (23)) (.leaf (24))) (.branch 59 (.leaf (25)) (.leaf (26)))) (.branch 66 (.branch 64 (.leaf (27)) (.leaf (28))) (.branch 68 (.leaf (29)) (.leaf (30))))))),
  (.branch 25 (.branch 2 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 67 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 58 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 69 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 42 (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 56 (.leaf (3)) (.branch 70 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-29)) (.leaf (-31)))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-23)) (.leaf (-24)))),
  (.branch 6 (.leaf (0)) (.leaf (-17))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-8)) (.leaf (-10)))),
  (.branch 11 (.leaf (0)) (.branch 34 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 69 (.leaf (-6)) (.leaf (-3))),
  (.branch 64 (.branch 61 (.branch 49 (.leaf (-31)) (.leaf (-30))) (.branch 62 (.leaf (-27)) (.branch 63 (.leaf (-24)) (.leaf (-21))))) (.branch 67 (.branch 65 (.leaf (-18)) (.branch 66 (.leaf (-15)) (.leaf (-12)))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 66 (.branch 64 (.branch 63 (.leaf (-24)) (.leaf (-21))) (.branch 65 (.leaf (-18)) (.leaf (-15)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-9))) (.branch 69 (.leaf (-6)) (.leaf (-3))))),
  (.branch 66 (.branch 42 (.leaf (-17)) (.branch 54 (.leaf (-16)) (.leaf (-15)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-9))) (.branch 69 (.leaf (-6)) (.leaf (-3))))),
  (.branch 68 (.branch 56 (.leaf (-10)) (.leaf (-9))) (.branch 69 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 66 (.branch 64 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_133_1068 : CycleWitness 8 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (2))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (7))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (2)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (5)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (6)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (1)) (.leaf (4))) (.branch 42 (.leaf (0)) (.leaf (3))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (2)) (.leaf (1))) (.branch 46 (.leaf (0)) (.leaf (7)))) (.branch 49 (.branch 48 (.leaf (5)) (.leaf (2))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (3))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (6))) (.branch 59 (.leaf (0)) (.branch 60 (.leaf (3)) (.leaf (2)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (1)) (.leaf (0))) (.branch 64 (.leaf (4)) (.leaf (5)))) (.branch 67 (.branch 66 (.leaf (1)) (.leaf (0))) (.branch 68 (.leaf (2)) (.branch 69 (.leaf (3)) (.leaf (7)))))))))
  code := certificateD8_1068
  counts := ![(.branch 32 (.branch 15 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))))) (.branch 50 (.branch 38 (.branch 36 (.leaf (10)) (.leaf (11))) (.branch 42 (.leaf (12)) (.branch 46 (.leaf (13)) (.leaf (14))))) (.branch 59 (.branch 54 (.leaf (15)) (.branch 57 (.leaf (16)) (.leaf (17)))) (.branch 63 (.leaf (18)) (.branch 67 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 10 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))) (.branch 51 (.branch 40 (.branch 37 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 62 (.branch 56 (.leaf (11)) (.leaf (12))) (.branch 66 (.leaf (13)) (.leaf (14)))))),
  (.branch 33 (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 39 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 61 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.branch 69 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4))))),
  (.branch 35 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 47 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 70 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 24 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-18)))) (.branch 38 (.leaf (-24)) (.branch 59 (.leaf (-28)) (.leaf (-34))))),
  (.branch 31 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 10 (.leaf (-17)) (.leaf (-18)))) (.branch 45 (.branch 40 (.leaf (-19)) (.leaf (-24))) (.branch 66 (.leaf (-25)) (.leaf (-26))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 14 (.leaf (-3)) (.branch 49 (.leaf (-4)) (.leaf (-5))))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-3)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 29 (.leaf (-17)) (.leaf (-18)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (-9)) (.leaf (-10)))),
  (.branch 35 (.branch 12 (.leaf (0)) (.leaf (-34))) (.branch 58 (.leaf (-35)) (.leaf (-36)))),
  (.branch 23 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 64 (.branch 60 (.leaf (-34)) (.leaf (-33))) (.branch 68 (.leaf (-32)) (.branch 69 (.leaf (-28)) (.leaf (-24))))),
  (.branch 68 (.branch 67 (.leaf (-26)) (.leaf (-23))) (.branch 69 (.leaf (-20)) (.leaf (-17)))),
  (.branch 62 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-3)))),
  (.branch 61 (.leaf (-5)) (.leaf (-4))),
  (.branch 67 (.branch 65 (.leaf (-18)) (.branch 66 (.leaf (-15)) (.leaf (-12)))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3))))),
  (.branch 67 (.branch 66 (.leaf (-10)) (.leaf (-8))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2))))),
  (.branch 64 (.branch 61 (.branch 59 (.leaf (-36)) (.branch 60 (.leaf (-33)) (.leaf (-30)))) (.branch 62 (.leaf (-27)) (.branch 63 (.leaf (-24)) (.leaf (-21))))) (.branch 67 (.branch 65 (.leaf (-18)) (.branch 66 (.leaf (-15)) (.leaf (-12)))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 24 (.leaf (-1)) (.leaf (0)))]
def witnessD8_133_1069 : CycleWitness 8 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (1)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (7)) (.branch 25 (.leaf (0)) (.leaf (2)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (3))) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (4)) (.leaf (0))) (.branch 33 (.leaf (5)) (.branch 34 (.leaf (1)) (.leaf (6)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (3)) (.leaf (1))) (.branch 42 (.leaf (4)) (.leaf (0))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (1)) (.leaf (5))) (.branch 46 (.leaf (0)) (.leaf (7)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (2))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (3))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (4))) (.branch 55 (.leaf (1)) (.leaf (5)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (6)) (.branch 60 (.leaf (0)) (.leaf (2)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (1)) (.leaf (3))) (.branch 64 (.leaf (0)) (.leaf (1)))) (.branch 67 (.branch 66 (.leaf (4)) (.leaf (0))) (.branch 68 (.leaf (5)) (.branch 69 (.leaf (1)) (.leaf (7)))))))))
  code := certificateD8_1069
  counts := ![(.branch 32 (.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))) (.branch 50 (.branch 39 (.branch 36 (.leaf (10)) (.leaf (11))) (.branch 43 (.leaf (12)) (.branch 46 (.leaf (13)) (.leaf (14))))) (.branch 60 (.branch 53 (.leaf (15)) (.branch 57 (.leaf (16)) (.leaf (17)))) (.branch 64 (.leaf (18)) (.branch 67 (.leaf (19)) (.leaf (20))))))),
  (.branch 34 (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))) (.branch 51 (.branch 41 (.branch 37 (.leaf (10)) (.leaf (11))) (.branch 44 (.leaf (12)) (.branch 48 (.leaf (13)) (.leaf (14))))) (.branch 62 (.branch 55 (.leaf (15)) (.branch 58 (.leaf (16)) (.leaf (17)))) (.branch 65 (.leaf (18)) (.branch 69 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 47 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 70 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-26)) (.leaf (-28)))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-20)) (.leaf (-21)))),
  (.branch 7 (.leaf (0)) (.leaf (-14))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (-5)) (.leaf (-7)))),
  (.branch 12 (.leaf (0)) (.branch 35 (.leaf (-34)) (.leaf (-35)))),
  (.leaf (0))]
  high := ![(.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2)))),
  (.branch 66 (.leaf (-3)) (.leaf (-2))),
  (.branch 65 (.branch 62 (.branch 50 (.leaf (-28)) (.leaf (-27))) (.branch 63 (.leaf (-24)) (.branch 64 (.leaf (-21)) (.leaf (-18))))) (.branch 67 (.branch 66 (.leaf (-15)) (.leaf (-12))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 66 (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-18)) (.leaf (-15)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-9))) (.branch 69 (.leaf (-6)) (.leaf (-3))))),
  (.branch 67 (.branch 43 (.leaf (-14)) (.branch 55 (.leaf (-13)) (.leaf (-12)))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.leaf (-7)) (.branch 69 (.leaf (-6)) (.leaf (-3)))),
  (.branch 64 (.branch 61 (.branch 36 (.leaf (-35)) (.branch 60 (.leaf (-33)) (.leaf (-30)))) (.branch 62 (.leaf (-27)) (.branch 63 (.leaf (-24)) (.leaf (-21))))) (.branch 67 (.branch 65 (.leaf (-18)) (.branch 66 (.leaf (-15)) (.leaf (-12)))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (0))]
def witnessD8_133_1070 : CycleWitness 8 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (7)) (.leaf (3))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (5))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (6)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (0)) (.leaf (5)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (7)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (3)) (.leaf (0))) (.branch 33 (.leaf (4)) (.branch 34 (.leaf (6)) (.leaf (5)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (3)) (.leaf (7))) (.branch 42 (.leaf (4)) (.leaf (0))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (5)) (.leaf (1))) (.branch 46 (.leaf (0)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (6)) (.leaf (3))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (4)) (.leaf (5))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (7)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (4)) (.branch 60 (.leaf (0)) (.leaf (5)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (6)) (.leaf (1))) (.branch 64 (.leaf (0)) (.leaf (2)))) (.branch 67 (.branch 66 (.leaf (3)) (.leaf (0))) (.branch 68 (.leaf (4)) (.branch 69 (.leaf (7)) (.leaf (5)))))))))
  code := certificateD8_1070
  counts := ![(.branch 32 (.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))) (.branch 50 (.branch 39 (.branch 36 (.leaf (10)) (.leaf (11))) (.branch 43 (.leaf (12)) (.branch 46 (.leaf (13)) (.leaf (14))))) (.branch 60 (.branch 53 (.leaf (15)) (.branch 57 (.leaf (16)) (.leaf (17)))) (.branch 64 (.leaf (18)) (.branch 67 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.branch 70 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 62 (.leaf (4)) (.leaf (5))))),
  (.branch 41 (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 55 (.leaf (3)) (.branch 69 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-27)) (.leaf (-30)))),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 5 (.leaf (0)) (.branch 31 (.leaf (-15)) (.leaf (-16)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-7)) (.leaf (-9)))),
  (.branch 17 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2)))),
  (.branch 65 (.branch 55 (.branch 46 (.leaf (-30)) (.leaf (-29))) (.branch 64 (.leaf (-28)) (.leaf (-24)))) (.branch 67 (.branch 66 (.leaf (-20)) (.leaf (-16))) (.branch 68 (.leaf (-12)) (.branch 69 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 66 (.branch 48 (.branch 39 (.leaf (-23)) (.leaf (-22))) (.branch 57 (.leaf (-21)) (.leaf (-20)))) (.branch 68 (.branch 67 (.leaf (-16)) (.leaf (-12))) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 68 (.branch 67 (.leaf (-16)) (.leaf (-12))) (.branch 69 (.leaf (-8)) (.leaf (-4)))),
  (.branch 60 (.leaf (-9)) (.branch 69 (.leaf (-8)) (.leaf (-4)))),
  (.branch 53 (.leaf (-2)) (.branch 62 (.leaf (-1)) (.leaf (0)))),
  (.branch 66 (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD8_133_1071 : CycleWitness 8 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (5))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (1))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (7))) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (1)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (5)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (4)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (7)) (.leaf (0))) (.branch 42 (.leaf (1)) (.leaf (3))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (4))) (.branch 46 (.leaf (2)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (5))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (3)) (.leaf (1))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (6))) (.branch 55 (.leaf (2)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (4)) (.leaf (1))) (.branch 59 (.leaf (0)) (.branch 60 (.leaf (3)) (.leaf (1)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (0)) (.leaf (7))) (.branch 64 (.leaf (2)) (.leaf (0)))) (.branch 67 (.branch 66 (.leaf (5)) (.leaf (1))) (.branch 68 (.leaf (0)) (.branch 69 (.leaf (3)) (.leaf (4)))))))))
  code := certificateD8_1071
  counts := ![(.branch 33 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 27 (.leaf (9)) (.branch 30 (.leaf (10)) (.leaf (11)))))) (.branch 50 (.branch 41 (.branch 36 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14)))) (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17))))) (.branch 59 (.branch 53 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20)))) (.branch 65 (.branch 62 (.leaf (21)) (.leaf (22))) (.branch 68 (.leaf (23)) (.leaf (24))))))),
  (.branch 32 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 52 (.branch 42 (.branch 37 (.leaf (7)) (.leaf (8))) (.branch 48 (.leaf (9)) (.leaf (10)))) (.branch 61 (.branch 58 (.leaf (11)) (.leaf (12))) (.branch 67 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.branch 69 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 70 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-23)) (.leaf (-33)))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-13)) (.leaf (-14)))) (.branch 52 (.branch 26 (.leaf (-16)) (.leaf (-22))) (.branch 61 (.leaf (-23)) (.leaf (-29))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-23)) (.leaf (-26)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-6)))),
  (.branch 10 (.leaf (0)) (.branch 45 (.leaf (-2)) (.leaf (-3)))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-20)) (.leaf (-22)))),
  (.branch 40 (.branch 19 (.leaf (0)) (.leaf (-6))) (.branch 63 (.leaf (-10)) (.leaf (-12))))]
  high := ![(.branch 54 (.branch 45 (.branch 42 (.leaf (-33)) (.leaf (-32))) (.branch 48 (.leaf (-31)) (.branch 51 (.leaf (-30)) (.leaf (-29))))) (.branch 63 (.branch 57 (.leaf (-28)) (.branch 60 (.leaf (-27)) (.leaf (-26)))) (.branch 66 (.leaf (-25)) (.branch 69 (.leaf (-24)) (.leaf (-12)))))),
  (.branch 68 (.branch 62 (.leaf (-29)) (.leaf (-26))) (.branch 69 (.leaf (-22)) (.leaf (-18)))),
  (.branch 66 (.branch 56 (.branch 47 (.leaf (-26)) (.leaf (-25))) (.branch 65 (.leaf (-24)) (.leaf (-20)))) (.branch 68 (.branch 67 (.leaf (-16)) (.leaf (-12))) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 52 (.leaf (-6)) (.branch 61 (.leaf (-5)) (.leaf (-4)))),
  (.branch 59 (.branch 58 (.leaf (-3)) (.leaf (-2))) (.branch 60 (.leaf (-1)) (.leaf (0)))),
  (.branch 68 (.branch 67 (.leaf (-8)) (.leaf (-6))) (.branch 69 (.leaf (-4)) (.leaf (-2)))),
  (.branch 61 (.branch 57 (.branch 55 (.branch 29 (.leaf (-22)) (.leaf (-21))) (.branch 56 (.leaf (-20)) (.leaf (-19)))) (.branch 59 (.branch 58 (.leaf (-18)) (.leaf (-17))) (.branch 60 (.leaf (-16)) (.leaf (-15))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (-14)) (.leaf (-13))) (.branch 64 (.leaf (-12)) (.leaf (-11)))) (.branch 67 (.branch 66 (.leaf (-10)) (.leaf (-9))) (.branch 68 (.leaf (-8)) (.branch 69 (.leaf (-7)) (.leaf (-6))))))),
  (.branch 66 (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-11)) (.leaf (-10)))) (.branch 68 (.branch 67 (.leaf (-9)) (.leaf (-8))) (.branch 69 (.leaf (-7)) (.leaf (-6)))))]
def witnessD8_133_1072 : CycleWitness 8 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (7))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (1)) (.leaf (0)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (3))) (.branch 29 (.leaf (6)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (4))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (3)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (5)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (7))) (.branch 42 (.leaf (3)) (.leaf (1))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (2))) (.branch 46 (.leaf (4)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (3))) (.branch 50 (.leaf (2)) (.branch 51 (.leaf (0)) (.leaf (6))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (4)) (.branch 60 (.leaf (1)) (.leaf (0)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (2)) (.leaf (3))) (.branch 64 (.leaf (7)) (.leaf (0)))) (.branch 67 (.branch 66 (.leaf (1)) (.leaf (5))) (.branch 68 (.leaf (0)) (.branch 69 (.leaf (2)) (.leaf (3)))))))))
  code := certificateD8_1072
  counts := ![(.branch 33 (.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))) (.branch 51 (.branch 40 (.branch 36 (.leaf (10)) (.leaf (11))) (.branch 44 (.leaf (12)) (.branch 47 (.leaf (13)) (.leaf (14))))) (.branch 61 (.branch 55 (.leaf (15)) (.branch 58 (.leaf (16)) (.leaf (17)))) (.branch 65 (.leaf (18)) (.branch 68 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 38 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 57 (.leaf (9)) (.leaf (10))) (.branch 69 (.leaf (11)) (.leaf (12)))))),
  (.branch 35 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 56 (.branch 42 (.leaf (5)) (.branch 49 (.leaf (6)) (.leaf (7)))) (.branch 63 (.leaf (8)) (.branch 70 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 53 (.leaf (3)) (.branch 67 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 33 (.branch 1 (.leaf (0)) (.branch 26 (.leaf (-13)) (.leaf (-14)))) (.branch 61 (.branch 36 (.leaf (-15)) (.leaf (-18))) (.branch 68 (.leaf (-19)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-23)) (.leaf (-27)))),
  (.branch 3 (.leaf (0)) (.branch 38 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 59 (.leaf (-10)) (.leaf (-11)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4)))),
  (.branch 29 (.branch 6 (.leaf (0)) (.leaf (-52))) (.branch 52 (.leaf (-53)) (.leaf (-54)))),
  (.branch 17 (.leaf (0)) (.leaf (-19)))]
  high := ![(.branch 69 (.leaf (-20)) (.leaf (-15))),
  (.branch 61 (.branch 49 (.leaf (-27)) (.branch 55 (.leaf (-26)) (.leaf (-25)))) (.branch 68 (.branch 67 (.leaf (-24)) (.leaf (-18))) (.branch 69 (.leaf (-12)) (.leaf (-6))))),
  (.branch 63 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 64 (.branch 61 (.branch 60 (.leaf (-11)) (.leaf (-10))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-8)) (.leaf (-7))))) (.branch 67 (.branch 65 (.leaf (-6)) (.branch 66 (.leaf (-5)) (.leaf (-4)))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 68 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1)))),
  (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (-54)) (.leaf (-51))) (.branch 55 (.leaf (-48)) (.leaf (-45)))) (.branch 58 (.branch 57 (.leaf (-42)) (.leaf (-39))) (.branch 59 (.leaf (-36)) (.branch 60 (.leaf (-33)) (.leaf (-30)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (-27)) (.leaf (-24))) (.branch 64 (.leaf (-21)) (.leaf (-18)))) (.branch 67 (.branch 66 (.leaf (-15)) (.leaf (-12))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 66 (.branch 18 (.leaf (-19)) (.branch 65 (.leaf (-18)) (.leaf (-15)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-9))) (.branch 69 (.leaf (-6)) (.leaf (-3)))))]
def witnessD8_133 : Fin 14 → CycleWitness 8 := ![witnessD8_133_1059, witnessD8_133_1060, witnessD8_133_1061, witnessD8_133_1062, witnessD8_133_1063, witnessD8_133_1064, witnessD8_133_1065, witnessD8_133_1066, witnessD8_133_1067, witnessD8_133_1068, witnessD8_133_1069, witnessD8_133_1070, witnessD8_133_1071, witnessD8_133_1072]
end RealPinwheel.FiveSixths


