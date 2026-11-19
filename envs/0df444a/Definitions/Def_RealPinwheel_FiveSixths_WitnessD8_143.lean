-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_143
-- name    : RealPinwheel_FiveSixths_WitnessD8_143
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:04:41.556543+00:00
-- url     : https://prove2.me/theorems/5167d922-001c-4537-996e-ea7a853d8771
-- title:
--   Exact witness block D8_143
-- statement:
--   These exact witnesses represent words 1202 through 1216 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1202–1216; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_143_1201 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (4)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (3)) (.leaf (7))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (5))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (7))) (.branch 40 (.leaf (1)) (.leaf (2))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (3))) (.branch 44 (.leaf (5)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (3)) (.leaf (6))) (.branch 52 (.leaf (0)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (4))) (.branch 56 (.leaf (0)) (.leaf (3))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (1)) (.leaf (2))) (.branch 60 (.leaf (0)) (.leaf (7)))) (.branch 63 (.branch 62 (.leaf (3)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (2)) (.leaf (5)))))))))
  code := certificateD8_1201
  counts := ![(.branch 31 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 30 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 32 (.branch 14 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 37 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 36 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 48 (.leaf (-15)) (.leaf (-18)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 25 (.leaf (-12)) (.branch 58 (.leaf (-14)) (.leaf (-15))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 41 (.leaf (-14)) (.leaf (-20)))),
  (.branch 29 (.branch 3 (.leaf (0)) (.leaf (-15))) (.branch 62 (.leaf (-19)) (.leaf (-22)))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 18 (.leaf (0)) (.branch 39 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 57 (.branch 49 (.leaf (-18)) (.branch 53 (.leaf (-17)) (.leaf (-16)))) (.branch 61 (.leaf (-15)) (.branch 65 (.leaf (-14)) (.leaf (-10))))),
  (.branch 64 (.branch 59 (.leaf (-15)) (.leaf (-14))) (.branch 65 (.leaf (-10)) (.leaf (-6)))),
  (.branch 48 (.branch 42 (.leaf (-20)) (.leaf (-19))) (.branch 54 (.leaf (-18)) (.branch 60 (.leaf (-17)) (.leaf (-16))))),
  (.branch 64 (.branch 63 (.leaf (-22)) (.leaf (-18))) (.branch 65 (.leaf (-14)) (.leaf (-10)))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 58 (.branch 54 (.branch 52 (.branch 29 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_143_1202 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (7)) (.leaf (3))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (4))) (.branch 19 (.leaf (6)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (7))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (2))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (5)) (.leaf (6)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (7))) (.branch 40 (.leaf (4)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (5))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (6)) (.leaf (3))) (.branch 48 (.leaf (1)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (4))) (.branch 52 (.leaf (7)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (5)) (.leaf (1))) (.branch 56 (.leaf (0)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (3)) (.leaf (6))) (.branch 60 (.leaf (0)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (4)) (.leaf (2))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (5)) (.leaf (7)))))))))
  code := certificateD8_1202
  counts := ![(.branch 31 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 28 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 66 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-23)) (.leaf (-26)))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 30 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-36)) (.leaf (-37)))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (-1))) (.branch 39 (.leaf (-2)) (.branch 52 (.leaf (-3)) (.leaf (-4)))))]
  high := ![(.branch 61 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 63 (.branch 42 (.leaf (-26)) (.branch 62 (.leaf (-25)) (.leaf (-20)))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 62 (.branch 60 (.branch 20 (.leaf (-37)) (.leaf (-35))) (.branch 61 (.leaf (-30)) (.leaf (-25)))) (.branch 64 (.branch 63 (.leaf (-20)) (.leaf (-15))) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 53 (.leaf (-4)) (.leaf (0)))]
def witnessD8_143_1203 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (4))) (.branch 15 (.leaf (2)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (7)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (2))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (4))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (2)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (4)) (.leaf (0))) (.branch 40 (.leaf (1)) (.leaf (5))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (7)) (.leaf (2))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (4))) (.branch 48 (.leaf (2)) (.leaf (5)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (3)) (.leaf (6)))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (4))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (5)) (.leaf (2))) (.branch 60 (.leaf (3)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (4))) (.branch 64 (.leaf (7)) (.branch 65 (.leaf (2)) (.leaf (5)))))))))
  code := certificateD8_1203
  counts := ![(.branch 28 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 19 (.leaf (-22)) (.branch 27 (.leaf (-23)) (.leaf (-24))))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 20 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 63 (.branch 62 (.leaf (-10)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 60 (.leaf (-3)) (.leaf (-2))),
  (.branch 63 (.branch 61 (.leaf (-24)) (.branch 62 (.leaf (-20)) (.leaf (-16)))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 64 (.branch 39 (.leaf (-13)) (.leaf (-12))) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.branch 50 (.leaf (-2)) (.leaf (0))),
  (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 65 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_143_1204 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (3)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (6))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (5)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (3)) (.leaf (7)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (4)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (5)) (.leaf (0))) (.branch 40 (.leaf (3)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (4)) (.leaf (0))) (.branch 44 (.leaf (2)) (.leaf (6)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (5)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (4)) (.leaf (2))) (.branch 52 (.leaf (0)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (7))) (.branch 56 (.leaf (2)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (4)) (.leaf (1))) (.branch 60 (.leaf (5)) (.leaf (3)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (2))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (4)) (.leaf (6)))))))))
  code := certificateD8_1204
  counts := ![(.branch 29 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 48 (.branch 39 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 43 (.leaf (9)) (.leaf (10)))) (.branch 57 (.branch 52 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 54 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 45 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 19 (.leaf (-17)) (.branch 52 (.leaf (-19)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 35 (.leaf (-15)) (.leaf (-21)))),
  (.branch 23 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 56 (.leaf (-16)) (.leaf (-19)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 46 (.leaf (-12)) (.leaf (-13)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 42 (.leaf (-4)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.branch 33 (.leaf (-10)) (.leaf (-11))))]
  high := ![(.branch 63 (.branch 53 (.leaf (-20)) (.branch 58 (.leaf (-19)) (.leaf (-18)))) (.branch 64 (.leaf (-14)) (.branch 65 (.leaf (-10)) (.leaf (-6))))),
  (.branch 36 (.leaf (-21)) (.branch 65 (.leaf (-20)) (.leaf (-16)))),
  (.branch 64 (.branch 57 (.leaf (-19)) (.leaf (-18))) (.branch 65 (.leaf (-14)) (.leaf (-10)))),
  (.branch 63 (.branch 62 (.leaf (-13)) (.leaf (-11))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-7)) (.leaf (-5))))),
  (.branch 43 (.leaf (-6)) (.leaf (-5))),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_143_1205 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (6))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (4))) (.branch 15 (.leaf (7)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (3)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (7))) (.branch 27 (.leaf (3)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (6)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (3)) (.leaf (7)))) (.branch 39 (.branch 38 (.leaf (4)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (5))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (6))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (4))) (.branch 48 (.leaf (7)) (.leaf (5)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (3)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (6)) (.leaf (4))) (.branch 56 (.leaf (0)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (5)) (.leaf (7))) (.branch 60 (.leaf (3)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (4))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (6)) (.leaf (5)))))))))
  code := certificateD8_1205
  counts := ![(.branch 29 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-16)) (.leaf (-17)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 20 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 19 (.leaf (-22)) (.branch 27 (.leaf (-23)) (.leaf (-24))))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 63 (.branch 57 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 63 (.branch 54 (.leaf (-17)) (.branch 62 (.leaf (-15)) (.leaf (-12)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 65 (.leaf (-6)) (.leaf (-3))),
  (.branch 63 (.branch 61 (.leaf (-24)) (.branch 62 (.leaf (-20)) (.leaf (-16)))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 64 (.branch 39 (.leaf (-13)) (.leaf (-12))) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.branch 50 (.leaf (-2)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_143_1206 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (0))) (.branch 19 (.leaf (5)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (2)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (2)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (4)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (6)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (2))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (3)) (.leaf (0))) (.branch 44 (.leaf (1)) (.leaf (7)))) (.branch 47 (.branch 46 (.leaf (5)) (.leaf (0))) (.branch 48 (.leaf (4)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (6)) (.leaf (3)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (0))) (.branch 56 (.leaf (2)) (.leaf (4))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (1)) (.leaf (0))) (.branch 60 (.leaf (5)) (.leaf (7)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (0))) (.branch 64 (.leaf (3)) (.branch 65 (.leaf (2)) (.leaf (6)))))))))
  code := certificateD8_1206
  counts := ![(.branch 30 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 47 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.branch 43 (.leaf (12)) (.leaf (13))))) (.branch 55 (.branch 51 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 29 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 39 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 32 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 66 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-17)) (.leaf (-22)))) (.branch 40 (.branch 10 (.leaf (-27)) (.leaf (-32))) (.branch 43 (.leaf (-36)) (.leaf (-41))))),
  (.branch 25 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))) (.branch 58 (.branch 29 (.leaf (-5)) (.leaf (-6))) (.branch 62 (.leaf (-7)) (.leaf (-8))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (-2))) (.branch 56 (.leaf (-9)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 24 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 57 (.leaf (-21)) (.leaf (-24)))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.branch 38 (.leaf (-1)) (.leaf (-5)))),
  (.branch 12 (.leaf (0)) (.branch 28 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 56 (.branch 48 (.branch 44 (.leaf (-41)) (.leaf (-40))) (.branch 52 (.leaf (-39)) (.leaf (-38)))) (.branch 64 (.branch 60 (.leaf (-37)) (.leaf (-36))) (.branch 65 (.leaf (-30)) (.leaf (-24))))),
  (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-5)))),
  (.branch 57 (.leaf (-14)) (.leaf (-13))),
  (.branch 65 (.leaf (-2)) (.leaf (-1))),
  (.branch 61 (.branch 59 (.branch 58 (.leaf (-24)) (.leaf (-22))) (.branch 60 (.leaf (-20)) (.leaf (-18)))) (.branch 63 (.branch 62 (.leaf (-16)) (.leaf (-14))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-10)) (.leaf (-8)))))),
  (.branch 62 (.branch 47 (.branch 6 (.leaf (-17)) (.leaf (-16))) (.branch 61 (.leaf (-15)) (.leaf (-13)))) (.branch 64 (.branch 63 (.leaf (-11)) (.leaf (-9))) (.branch 65 (.leaf (-7)) (.leaf (-5))))),
  (.branch 53 (.branch 39 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-2)) (.leaf (0)))),
  (.branch 63 (.branch 62 (.leaf (-10)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2)))))]
def witnessD8_143_1207 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (7))) (.branch 23 (.leaf (0)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (6)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (5)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (1)) (.leaf (2))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (4))) (.branch 44 (.leaf (7)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (3))) (.branch 52 (.leaf (0)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (6))) (.branch 56 (.leaf (0)) (.leaf (4))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (1)) (.leaf (2))) (.branch 60 (.leaf (0)) (.leaf (3)))) (.branch 63 (.branch 62 (.leaf (5)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (2)) (.leaf (7)))))))))
  code := certificateD8_1207
  counts := ![(.branch 31 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 30 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 32 (.branch 14 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 37 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 62 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 48 (.leaf (-15)) (.leaf (-18)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 25 (.leaf (-12)) (.branch 58 (.leaf (-14)) (.leaf (-15))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 41 (.leaf (-14)) (.leaf (-20)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-21)) (.leaf (-23)))),
  (.branch 36 (.branch 10 (.leaf (0)) (.leaf (-7))) (.branch 62 (.leaf (-9)) (.leaf (-11)))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 57 (.branch 49 (.leaf (-18)) (.branch 53 (.leaf (-17)) (.leaf (-16)))) (.branch 61 (.leaf (-15)) (.branch 65 (.leaf (-14)) (.leaf (-10))))),
  (.branch 64 (.branch 59 (.leaf (-15)) (.leaf (-14))) (.branch 65 (.leaf (-10)) (.leaf (-6)))),
  (.branch 48 (.branch 42 (.leaf (-20)) (.leaf (-19))) (.branch 54 (.leaf (-18)) (.branch 60 (.leaf (-17)) (.leaf (-16))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 44 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-19)) (.leaf (-17))))) (.branch 63 (.branch 61 (.leaf (-15)) (.branch 62 (.leaf (-13)) (.leaf (-11)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-7)) (.leaf (-5)))))),
  (.branch 64 (.branch 63 (.leaf (-11)) (.leaf (-9))) (.branch 65 (.leaf (-7)) (.leaf (-5)))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_143_1208 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (6))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (7)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (6)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (4)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (5)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (7))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (1)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (5))) (.branch 52 (.leaf (0)) (.leaf (3)))) (.branch 55 (.branch 54 (.leaf (6)) (.leaf (1))) (.branch 56 (.leaf (0)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (4)) (.leaf (3))) (.branch 60 (.leaf (0)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (5)) (.leaf (0))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (7)) (.leaf (3)))))))))
  code := certificateD8_1208
  counts := ![(.branch 30 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 39 (.leaf (5)) (.branch 46 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 43 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-9)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-23))) (.branch 28 (.leaf (-24)) (.leaf (-25)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-13)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-12))),
  (.branch 21 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 63 (.branch 62 (.leaf (-25)) (.leaf (-20))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 58 (.branch 51 (.leaf (-14)) (.leaf (-12))) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.branch 40 (.leaf (-3)) (.branch 60 (.leaf (-2)) (.leaf (0)))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_143_1209 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (3)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (4))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (5))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (2))) (.branch 19 (.leaf (6)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (7))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (4)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (5)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (4))) (.branch 40 (.leaf (3)) (.leaf (6))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (5))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (1)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (2))) (.branch 52 (.leaf (7)) (.leaf (3)))) (.branch 55 (.branch 54 (.leaf (4)) (.leaf (1))) (.branch 56 (.leaf (0)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (5)) (.leaf (3))) (.branch 60 (.leaf (0)) (.leaf (4)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (6))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (5)) (.leaf (3)))))))))
  code := certificateD8_1209
  counts := ![(.branch 27 (.branch 12 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 40 (.leaf (5)) (.branch 46 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 54 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 41 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 27 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 16 (.leaf (-7)) (.leaf (-8)))) (.branch 49 (.branch 38 (.leaf (-9)) (.leaf (-10))) (.branch 60 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-23)) (.leaf (-24)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 17 (.leaf (-14)) (.leaf (-15)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 19 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-11)) (.leaf (-10)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7))))),
  (.branch 63 (.branch 49 (.leaf (-24)) (.branch 56 (.leaf (-22)) (.leaf (-20)))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 58 (.branch 38 (.leaf (-13)) (.leaf (-12))) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.branch 60 (.leaf (-2)) (.leaf (0))),
  (.branch 63 (.branch 62 (.leaf (-15)) (.leaf (-12))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 51 (.leaf (-4)) (.leaf (-3))),
  (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_143_1210 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (7))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (2)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (7)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (5)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (3)) (.leaf (0))) (.branch 40 (.leaf (1)) (.leaf (6))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (4)) (.leaf (2))) (.branch 44 (.leaf (0)) (.leaf (3)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (7))) (.branch 48 (.leaf (0)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (1))) (.branch 52 (.leaf (3)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (4))) (.branch 56 (.leaf (6)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (3))) (.branch 60 (.leaf (2)) (.leaf (5)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (0))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (7)) (.leaf (3)))))))))
  code := certificateD8_1210
  counts := ![(.branch 30 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 48 (.branch 39 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 38 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 61 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-26)) (.leaf (-27)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 31 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 64 (.leaf (-9)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.branch 38 (.leaf (-7)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 28 (.leaf (-21)) (.leaf (-25)))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (-9))) (.branch 61 (.leaf (-10)) (.leaf (-13)))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (-9))) (.branch 56 (.leaf (-11)) (.leaf (-12)))),
  (.branch 14 (.leaf (0)) (.branch 47 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 59 (.branch 49 (.leaf (-27)) (.branch 54 (.leaf (-25)) (.leaf (-23)))) (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-14)) (.leaf (-7))))),
  (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 65 (.leaf (-12)) (.leaf (-9))),
  (.branch 53 (.branch 39 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8)))) (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-3)) (.leaf (0))))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-25)) (.leaf (-23))) (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-19)) (.leaf (-17))))) (.branch 63 (.branch 61 (.leaf (-15)) (.branch 62 (.leaf (-13)) (.leaf (-11)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-7)) (.leaf (-5)))))),
  (.branch 63 (.branch 62 (.leaf (-13)) (.leaf (-11))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-7)) (.leaf (-5))))),
  (.branch 61 (.branch 58 (.branch 57 (.leaf (-12)) (.leaf (-11))) (.branch 59 (.leaf (-10)) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 63 (.branch 62 (.leaf (-7)) (.leaf (-6))) (.branch 64 (.leaf (-5)) (.branch 65 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 48 (.leaf (-4)) (.leaf (-3)))]
def witnessD8_143_1211 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (1)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (1)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (3)) (.leaf (7))) (.branch 40 (.leaf (5)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (1))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (4)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (6)) (.leaf (3))) (.branch 52 (.leaf (0)) (.leaf (5)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (2))) (.branch 56 (.leaf (0)) (.leaf (3))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (1)) (.leaf (0))) (.branch 60 (.leaf (4)) (.leaf (7)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (0))) (.branch 64 (.leaf (3)) (.branch 65 (.leaf (1)) (.leaf (5)))))))))
  code := certificateD8_1211
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 32 (.branch 14 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 38 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 40 (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 53 (.leaf (3)) (.branch 66 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))) (.branch 47 (.branch 36 (.leaf (-5)) (.leaf (-6))) (.branch 58 (.leaf (-7)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.leaf (-23))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-8))) (.branch 24 (.leaf (-11)) (.leaf (-12)))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (-31))) (.branch 33 (.leaf (-32)) (.branch 46 (.leaf (-33)) (.leaf (-34))))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 64 (.branch 60 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 59 (.leaf (-8)) (.leaf (-7))),
  (.branch 63 (.branch 36 (.leaf (-23)) (.branch 56 (.leaf (-22)) (.leaf (-20)))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 58 (.leaf (-12)) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.branch 47 (.leaf (-34)) (.branch 61 (.leaf (-30)) (.leaf (-25)))) (.branch 64 (.branch 63 (.leaf (-20)) (.leaf (-15))) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_143_1212 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (1))) (.branch 31 (.leaf (7)) (.branch 32 (.leaf (0)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (1)) (.leaf (2))) (.branch 36 (.leaf (0)) (.leaf (4)))) (.branch 39 (.branch 38 (.leaf (1)) (.leaf (2))) (.branch 40 (.leaf (3)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (5)) (.leaf (1))) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (1))) (.branch 48 (.leaf (3)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (4))) (.branch 52 (.leaf (1)) (.leaf (6)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (3))) (.branch 56 (.leaf (1)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (4))) (.branch 60 (.leaf (1)) (.leaf (2)))) (.branch 63 (.branch 62 (.leaf (3)) (.leaf (0))) (.branch 64 (.leaf (7)) (.branch 65 (.leaf (1)) (.leaf (4)))))))))
  code := certificateD8_1212
  counts := ![(.branch 32 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 49 (.branch 41 (.branch 36 (.leaf (8)) (.leaf (9))) (.branch 45 (.leaf (10)) (.leaf (11)))) (.branch 58 (.branch 54 (.leaf (12)) (.leaf (13))) (.branch 63 (.leaf (14)) (.leaf (15)))))),
  (.branch 34 (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))) (.branch 52 (.branch 43 (.branch 38 (.leaf (8)) (.leaf (9))) (.branch 47 (.leaf (10)) (.leaf (11)))) (.branch 60 (.branch 56 (.leaf (12)) (.leaf (13))) (.branch 65 (.leaf (14)) (.leaf (15)))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 37 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 44 (.leaf (5)) (.leaf (6))) (.branch 59 (.leaf (7)) (.branch 66 (.leaf (8)) (.leaf (9)))))),
  (.branch 9 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 53 (.leaf (1)) (.leaf (2)))),
  (.branch 31 (.leaf (0)) (.branch 64 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-17)) (.leaf (-19)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-7)) (.leaf (-8)))),
  (.branch 28 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-6)) (.leaf (-7)))) (.branch 50 (.branch 39 (.leaf (-8)) (.leaf (-9))) (.branch 61 (.leaf (-10)) (.leaf (-11))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 18 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-24))),
  (.branch 20 (.leaf (0)) (.leaf (-13))),
  (.branch 31 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 59 (.branch 50 (.leaf (-19)) (.leaf (-18))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 61 (.leaf (-8)) (.leaf (-5))),
  (.branch 63 (.branch 62 (.leaf (-11)) (.leaf (-10))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7))))),
  (.branch 64 (.branch 63 (.leaf (-12)) (.leaf (-9))) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 52 (.leaf (-1)) (.leaf (0))),
  (.branch 54 (.branch 48 (.branch 45 (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22)))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19))))) (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 65 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_143_1213 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (5))) (.branch 7 (.leaf (0)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (6))) (.branch 15 (.leaf (2)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (0))) (.branch 19 (.leaf (3)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (7))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (6)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (4)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (2)) (.leaf (5))) (.branch 40 (.leaf (0)) (.leaf (7))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (3)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (4)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (6))) (.branch 48 (.leaf (3)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (0))) (.branch 52 (.leaf (2)) (.leaf (4)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (7))) (.branch 56 (.leaf (3)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (6)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (5)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (4))) (.branch 64 (.leaf (3)) (.branch 65 (.leaf (1)) (.leaf (6)))))))))
  code := certificateD8_1213
  counts := ![(.branch 29 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 60 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 30 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 14 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 58 (.branch 47 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 15 (.leaf (-19)) (.branch 44 (.leaf (-24)) (.leaf (-29))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-8))) (.branch 48 (.leaf (-13)) (.leaf (-17)))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 36 (.leaf (-7)) (.branch 53 (.leaf (-9)) (.leaf (-10))))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 33 (.branch 25 (.leaf (0)) (.leaf (-1))) (.branch 58 (.leaf (-6)) (.leaf (-7)))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (-10))) (.branch 55 (.leaf (-14)) (.leaf (-17))))]
  high := ![(.branch 63 (.branch 35 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 60 (.leaf (-3)) (.leaf (-2))),
  (.branch 62 (.branch 53 (.branch 45 (.leaf (-29)) (.leaf (-28))) (.branch 61 (.leaf (-27)) (.leaf (-24)))) (.branch 64 (.branch 63 (.leaf (-21)) (.leaf (-18))) (.branch 65 (.leaf (-15)) (.leaf (-12))))),
  (.branch 57 (.branch 49 (.leaf (-17)) (.leaf (-16))) (.branch 65 (.leaf (-15)) (.leaf (-12)))),
  (.branch 64 (.branch 54 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-7)))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-7)) (.leaf (-6))) (.branch 61 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.branch 63 (.leaf (-3)) (.leaf (-2))) (.branch 65 (.leaf (-1)) (.leaf (0))))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-17)) (.leaf (-16))) (.branch 58 (.leaf (-15)) (.branch 59 (.leaf (-14)) (.leaf (-13))))) (.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-11)) (.leaf (-10)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7))))))]
def witnessD8_143_1214 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (1))) (.branch 15 (.leaf (7)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (0))) (.branch 19 (.leaf (3)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (6))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (5)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (7))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (1)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (5)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (3)) (.leaf (6))) (.branch 40 (.leaf (0)) (.leaf (4))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (1))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (5)) (.leaf (1))) (.branch 48 (.leaf (7)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (4)) (.leaf (0))) (.branch 52 (.leaf (3)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (5))) (.branch 56 (.leaf (0)) (.leaf (6))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (3)) (.leaf (1))) (.branch 60 (.leaf (4)) (.leaf (2)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (7))) (.branch 64 (.leaf (5)) (.branch 65 (.leaf (1)) (.leaf (3)))))))))
  code := certificateD8_1214
  counts := ![(.branch 29 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 14 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 38 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.leaf (7))))),
  (.branch 36 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 55 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 64 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 47 (.leaf (-9)) (.leaf (-12)))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-19))) (.branch 54 (.leaf (-24)) (.leaf (-27)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 38 (.leaf (-3)) (.branch 44 (.leaf (-4)) (.leaf (-5))))),
  (.branch 3 (.leaf (0)) (.branch 31 (.leaf (-45)) (.leaf (-47)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (-10))) (.branch 64 (.leaf (-13)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.branch 39 (.leaf (-11)) (.leaf (-12)))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (-2))) (.branch 63 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 63 (.branch 57 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 54 (.branch 48 (.leaf (-12)) (.leaf (-11))) (.branch 60 (.leaf (-10)) (.leaf (-9)))),
  (.branch 63 (.branch 55 (.leaf (-27)) (.branch 62 (.leaf (-26)) (.leaf (-22)))) (.branch 64 (.leaf (-18)) (.branch 65 (.leaf (-14)) (.leaf (-10))))),
  (.branch 61 (.branch 59 (.leaf (-5)) (.branch 60 (.leaf (-4)) (.leaf (-3)))) (.branch 62 (.leaf (-2)) (.branch 63 (.leaf (-1)) (.leaf (0))))),
  (.branch 62 (.branch 51 (.branch 32 (.leaf (-47)) (.leaf (-46))) (.branch 61 (.leaf (-42)) (.leaf (-35)))) (.branch 64 (.branch 63 (.leaf (-28)) (.leaf (-21))) (.branch 65 (.leaf (-14)) (.leaf (-7))))),
  (.branch 65 (.leaf (-14)) (.leaf (-7))),
  (.branch 61 (.branch 58 (.branch 40 (.leaf (-12)) (.leaf (-11))) (.branch 59 (.leaf (-10)) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 63 (.branch 62 (.leaf (-7)) (.leaf (-6))) (.branch 64 (.leaf (-5)) (.branch 65 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 64 (.leaf (-5)) (.branch 65 (.leaf (-4)) (.leaf (-3))))]
def witnessD8_143_1215 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (7))) (.branch 15 (.leaf (1)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (0))) (.branch 19 (.leaf (4)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (6))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (1))) (.branch 27 (.leaf (4)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (7))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (4)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (6)) (.leaf (2))) (.branch 40 (.leaf (0)) (.leaf (5))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (3)) (.leaf (1))) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (7))) (.branch 48 (.leaf (1)) (.leaf (5)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (3)) (.leaf (0))) (.branch 52 (.leaf (4)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (6))) (.branch 56 (.leaf (0)) (.leaf (3))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (5)) (.leaf (1))) (.branch 60 (.leaf (4)) (.leaf (2)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (7))) (.branch 64 (.leaf (3)) (.branch 65 (.leaf (1)) (.leaf (5)))))))))
  code := certificateD8_1215
  counts := ![(.branch 29 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-16)) (.leaf (-17)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 20 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 19 (.leaf (-22)) (.branch 27 (.leaf (-23)) (.leaf (-24))))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 14 (.leaf (0)) (.branch 30 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 63 (.branch 57 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 60 (.leaf (-3)) (.leaf (-2))),
  (.branch 63 (.branch 54 (.leaf (-17)) (.branch 62 (.leaf (-15)) (.leaf (-12)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 65 (.leaf (-6)) (.leaf (-3))),
  (.branch 63 (.branch 61 (.leaf (-24)) (.branch 62 (.leaf (-20)) (.leaf (-16)))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 50 (.leaf (-2)) (.leaf (0))),
  (.branch 60 (.branch 57 (.branch 39 (.leaf (-23)) (.branch 56 (.leaf (-22)) (.leaf (-20)))) (.branch 58 (.leaf (-18)) (.branch 59 (.leaf (-16)) (.leaf (-14))))) (.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-10)) (.leaf (-8)))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))]
def witnessD8_143 : Fin 15 → CycleWitness 8 := ![witnessD8_143_1201, witnessD8_143_1202, witnessD8_143_1203, witnessD8_143_1204, witnessD8_143_1205, witnessD8_143_1206, witnessD8_143_1207, witnessD8_143_1208, witnessD8_143_1209, witnessD8_143_1210, witnessD8_143_1211, witnessD8_143_1212, witnessD8_143_1213, witnessD8_143_1214, witnessD8_143_1215]
end RealPinwheel.FiveSixths


