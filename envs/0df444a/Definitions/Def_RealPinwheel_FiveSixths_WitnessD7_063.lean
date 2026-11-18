-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_063
-- name    : RealPinwheel_FiveSixths_WitnessD7_063
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:15:21.152371+00:00
-- url     : https://prove2.me/theorems/1411dcb9-4bf0-4c5f-9c54-40c50992df50
-- title:
--   Exact witness block D7_063
-- statement:
--   These exact witnesses represent words 1197 through 1231 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 1197–1231; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_063_1196 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (5))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1196
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-18))) (.branch 24 (.leaf (-19)) (.leaf (-20)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-3)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 21 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.branch 25 (.leaf (-20)) (.leaf (-15))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.branch 11 (.leaf (-6)) (.leaf (-5))),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_063_1197 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1197
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 20 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-16)) (.leaf (-17)))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 19 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 4 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-11)))),
  (.branch 26 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 25 (.branch 14 (.leaf (-17)) (.branch 24 (.leaf (-15)) (.leaf (-12)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 16 (.branch 10 (.branch 7 (.branch 6 (.leaf (-23)) (.leaf (-22))) (.branch 8 (.leaf (-21)) (.branch 9 (.leaf (-20)) (.leaf (-19))))) (.branch 13 (.branch 11 (.leaf (-18)) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))))) (.branch 22 (.branch 19 (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_063_1198 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1198
  counts := ![(.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.leaf (12)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 25 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 25 (.leaf (-5)) (.leaf (-3))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-17)) (.leaf (-16))) (.branch 14 (.leaf (-15)) (.leaf (-14)))) (.branch 17 (.branch 16 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-11)) (.leaf (-10))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_063_1199 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1199
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-18))) (.branch 24 (.leaf (-19)) (.leaf (-20)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-3)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 25 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 21 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.branch 25 (.leaf (-20)) (.leaf (-15))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.branch 11 (.leaf (-6)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-17)) (.leaf (-16))) (.branch 14 (.leaf (-15)) (.leaf (-14)))) (.branch 17 (.branch 16 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-11)) (.leaf (-10))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_063_1200 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (6)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (5)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1200
  counts := ![(.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 6 (.leaf (-20)) (.leaf (-21)))),
  (.branch 2 (.leaf (0)) (.branch 12 (.leaf (-15)) (.leaf (-21)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.branch 17 (.leaf (-1)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (-6)) (.leaf (-7)))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 23 (.branch 7 (.leaf (-21)) (.leaf (-20))) (.branch 27 (.leaf (-15)) (.leaf (-9)))),
  (.branch 25 (.branch 13 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-11)) (.leaf (-7))))),
  (.leaf (0)),
  (.branch 18 (.leaf (-4)) (.leaf (-3))),
  (.branch 25 (.branch 24 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.branch 21 (.branch 6 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_063_1201 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (2)))))))
  code := certificateD7_1201
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-4)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 25 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-24))),
  (.branch 18 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 21 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 25 (.leaf (-6)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-17)) (.leaf (-16))) (.branch 14 (.leaf (-15)) (.leaf (-14)))) (.branch 17 (.branch 16 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-11)) (.leaf (-10))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 10 (.branch 7 (.branch 5 (.leaf (-24)) (.branch 6 (.leaf (-23)) (.leaf (-22)))) (.branch 8 (.leaf (-21)) (.branch 9 (.leaf (-20)) (.leaf (-19))))) (.branch 13 (.branch 11 (.leaf (-18)) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))))) (.branch 22 (.branch 19 (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_063_1202 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (4))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (6))) (.branch 27 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1202
  counts := ![(.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 25 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.leaf (12)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 12 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 18 (.leaf (-5)) (.branch 23 (.leaf (-4)) (.leaf (-3)))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 15 (.leaf (-14)) (.leaf (-12))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_063_1203 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (1)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (6)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (4))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (5))) (.branch 27 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1203
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 24 (.leaf (9)) (.branch 27 (.leaf (10)) (.leaf (11)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (-9)) (.leaf (-11)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-10)) (.leaf (-11))))]
  high := ![(.branch 17 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 25 (.leaf (-10)) (.leaf (-8)))),
  (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3)))),
  (.branch 19 (.leaf (-2)) (.leaf (0))),
  (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-9))) (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-5)) (.leaf (-3))))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_063_1204 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (4)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1204
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 20 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.leaf (-20))),
  (.branch 22 (.leaf (0)) (.leaf (-6))),
  (.branch 14 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 19 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5))))),
  (.branch 27 (.leaf (-4)) (.leaf (-2))),
  (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3)))),
  (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-20)) (.leaf (-19))) (.branch 11 (.leaf (-18)) (.branch 12 (.leaf (-17)) (.leaf (-16))))) (.branch 15 (.branch 14 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-13)) (.branch 17 (.leaf (-12)) (.leaf (-11)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 17 (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))) (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.leaf (-8))))) (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_063_1205 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1205
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 17 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 27 (.leaf (-10)) (.leaf (-5))),
  (.branch 20 (.leaf (-4)) (.branch 24 (.leaf (-3)) (.leaf (-2)))),
  (.branch 26 (.branch 9 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.branch 24 (.branch 7 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7)))) (.branch 26 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.leaf (-3))))),
  (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-17)) (.leaf (-16))) (.branch 14 (.leaf (-15)) (.leaf (-14)))) (.branch 17 (.branch 16 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-11)) (.leaf (-10))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_063_1206 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (4)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (5)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1206
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-22))),
  (.branch 13 (.leaf (0)) (.leaf (-15))),
  (.branch 20 (.leaf (0)) (.leaf (-8))),
  (.branch 27 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 26 (.leaf (-6)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 27 (.leaf (-4)) (.leaf (-2))),
  (.branch 25 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.branch 11 (.branch 8 (.branch 7 (.leaf (-22)) (.leaf (-21))) (.branch 9 (.leaf (-20)) (.branch 10 (.leaf (-19)) (.leaf (-18))))) (.branch 14 (.branch 12 (.leaf (-17)) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 20 (.branch 16 (.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_063_1207 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (6)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1207
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-5)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-18))),
  (.branch 24 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 26 (.leaf (-6)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 20 (.leaf (-4)) (.branch 24 (.leaf (-3)) (.leaf (-2)))),
  (.branch 22 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 19 (.branch 14 (.branch 12 (.branch 11 (.leaf (-18)) (.leaf (-17))) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 16 (.branch 15 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_063_1208 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1208
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 14 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 19 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5))))),
  (.branch 27 (.leaf (-4)) (.leaf (-2))),
  (.branch 26 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 17 (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))) (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.leaf (-8))))) (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_063_1209 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (6)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1209
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-19))),
  (.branch 23 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 19 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5))))),
  (.branch 26 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.branch 23 (.leaf (-3)) (.leaf (-2))) (.branch 25 (.leaf (-1)) (.leaf (0)))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 13 (.branch 11 (.branch 10 (.leaf (-19)) (.leaf (-18))) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 15 (.branch 14 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-13)) (.branch 17 (.leaf (-12)) (.leaf (-11)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_063_1210 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (6)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (6)) (.leaf (4)))))))
  code := certificateD7_1210
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (-13))) (.branch 23 (.leaf (-14)) (.leaf (-15)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 26 (.leaf (-6)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 24 (.leaf (-15)) (.leaf (-12))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_063_1211 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (6)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (5)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1211
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-18)) (.leaf (-23)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-19))) (.branch 21 (.leaf (-20)) (.leaf (-21)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (-3)) (.leaf (-5)))),
  (.branch 13 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 18 (.branch 12 (.leaf (-23)) (.branch 15 (.leaf (-22)) (.leaf (-21)))) (.branch 24 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 27 (.leaf (-18)) (.leaf (-11))))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-18)) (.leaf (-15)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 25 (.branch 6 (.leaf (-13)) (.leaf (-12))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-1))]
def witnessD7_063_1212 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (6)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (5)))))))
  code := certificateD7_1212
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 27 (.leaf (-10)) (.leaf (-5))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 4 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-15)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 18 (.leaf (-5)) (.leaf (-3))),
  (.branch 26 (.branch 15 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.leaf (-3)))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_063_1213 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (6))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (5))) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (4)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (6))) (.branch 27 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1213
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 26 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_063_1214 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (5))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1214
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 21 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-21)))]
  high := ![(.branch 23 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 17 (.leaf (-3)) (.leaf (-2))),
  (.branch 26 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 5 (.leaf (-16)) (.branch 24 (.leaf (-15)) (.leaf (-12)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 19 (.leaf (-2)) (.leaf (0))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 10 (.leaf (-19)) (.branch 11 (.leaf (-18)) (.leaf (-17))))) (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_063_1215 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (3))) (.branch 13 (.leaf (1)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (5)) (.branch 23 (.leaf (3)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (2))) (.branch 27 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1215
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-11)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 22 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 25 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.leaf (-4)) (.leaf (-3))),
  (.branch 21 (.branch 15 (.leaf (-14)) (.leaf (-12))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-20)) (.leaf (-19))) (.branch 11 (.leaf (-18)) (.branch 12 (.leaf (-17)) (.leaf (-16))))) (.branch 15 (.branch 14 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-13)) (.branch 17 (.leaf (-12)) (.leaf (-11)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_063_1216 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (6))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (5)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (3))) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (4)) (.branch 23 (.leaf (1)) (.leaf (6)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1216
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-14)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-6))))]
  high := ![(.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 27 (.leaf (-7)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 24 (.branch 8 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 19 (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))) (.branch 20 (.leaf (-11)) (.branch 21 (.leaf (-10)) (.leaf (-9))))) (.branch 25 (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 26 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.leaf (-3))))]
def witnessD7_063_1217 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (6)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (4)) (.branch 23 (.leaf (0)) (.leaf (6)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1217
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 19 (.leaf (-8)) (.leaf (-9)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 15 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-10)))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-10)) (.leaf (-11)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 20 (.leaf (-9)) (.branch 24 (.leaf (-8)) (.leaf (-7)))),
  (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3)))),
  (.branch 15 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 27 (.leaf (-7)) (.leaf (-4))))),
  (.branch 19 (.leaf (-2)) (.leaf (0))),
  (.branch 24 (.branch 8 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_063_1218 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (6)) (.leaf (3))) (.branch 13 (.leaf (1)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (4)) (.branch 23 (.leaf (3)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (2))) (.branch 27 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1218
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-11)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 25 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.leaf (-4)) (.leaf (-3))),
  (.branch 21 (.branch 15 (.leaf (-14)) (.leaf (-12))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_063_1219 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (4)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (5)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (4))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (5)) (.branch 23 (.leaf (3)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (6)) (.leaf (4)))))))
  code := certificateD7_1219
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (-13))) (.branch 23 (.leaf (-14)) (.leaf (-15)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-16))) (.branch 22 (.leaf (-17)) (.leaf (-18)))),
  (.branch 8 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 21 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 24 (.leaf (-15)) (.leaf (-12))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-15)) (.leaf (-12)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 9 (.leaf (-4)) (.leaf (-3)))]
def witnessD7_063_1220 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (6)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (4))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (2))) (.branch 27 (.leaf (3)) (.leaf (4)))))))
  code := certificateD7_1220
  counts := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-23))) (.branch 17 (.leaf (-26)) (.leaf (-27)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-18))) (.branch 24 (.leaf (-19)) (.leaf (-20)))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-3)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 25 (.branch 18 (.leaf (-27)) (.branch 24 (.leaf (-25)) (.leaf (-20)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.branch 25 (.leaf (-20)) (.leaf (-15))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.branch 21 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.branch 11 (.leaf (-6)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_063_1221 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (6)) (.leaf (1))) (.branch 13 (.leaf (3)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (4)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (6)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1221
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-10)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 19 (.leaf (-9)) (.leaf (-11)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-10)) (.leaf (-11)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 19 (.leaf (-11)) (.leaf (-10))),
  (.branch 27 (.leaf (-4)) (.leaf (-3))),
  (.branch 26 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 27 (.leaf (-7)) (.leaf (-4)))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 23 (.branch 21 (.branch 6 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_063_1222 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (1)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (5)) (.branch 23 (.leaf (4)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (4)))))))
  code := certificateD7_1222
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-19))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-18)) (.leaf (-19)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 27 (.leaf (-5)) (.leaf (-6)))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 12 (.branch 2 (.leaf (-19)) (.branch 7 (.leaf (-18)) (.leaf (-17)))) (.branch 22 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-9))))),
  (.branch 20 (.branch 14 (.leaf (-19)) (.leaf (-17))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-6)),
  (.branch 15 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 24 (.branch 13 (.leaf (-14)) (.branch 23 (.leaf (-13)) (.leaf (-11)))) (.branch 26 (.branch 25 (.leaf (-9)) (.leaf (-7))) (.branch 27 (.leaf (-5)) (.leaf (-3))))),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_063_1223 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (4)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (6)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (3)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1223
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-18))) (.branch 11 (.leaf (-22)) (.branch 21 (.leaf (-23)) (.leaf (-28))))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 20 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 26 (.branch 22 (.leaf (-28)) (.leaf (-25))) (.branch 27 (.leaf (-18)) (.leaf (-11)))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 10 (.leaf (-19)) (.branch 11 (.leaf (-18)) (.leaf (-17))))) (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_063_1224 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (6)) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (5)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1224
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 16 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 17 (.leaf (-8)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-19)) (.leaf (-20)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 19 (.branch 2 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5))))),
  (.branch 20 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3)))),
  (.branch 26 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 27 (.leaf (-8)) (.leaf (-6)))),
  (.branch 24 (.branch 13 (.leaf (-20)) (.branch 23 (.leaf (-18)) (.leaf (-15)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_063_1225 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (4)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (6)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1225
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-20))),
  (.branch 22 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 19 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5))))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.leaf (-1)) (.leaf (0))),
  (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-20)) (.leaf (-19))) (.branch 11 (.leaf (-18)) (.branch 12 (.leaf (-17)) (.leaf (-16))))) (.branch 15 (.branch 14 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-13)) (.branch 17 (.leaf (-12)) (.leaf (-11)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_063_1226 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (1)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1226
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-18)) (.leaf (-21)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 21 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 14 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 26 (.leaf (-6)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 22 (.leaf (-7)) (.leaf (-5))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 21 (.branch 17 (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))) (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.leaf (-8))))) (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_063_1227 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (5))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (6))) (.branch 27 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1227
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-16))),
  (.branch 26 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 19 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5))))),
  (.branch 26 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 16 (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_063_1228 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (1)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (6)) (.leaf (3)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1228
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-19))),
  (.branch 23 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 23 (.branch 19 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 13 (.branch 11 (.branch 10 (.leaf (-19)) (.leaf (-18))) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 15 (.branch 14 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-13)) (.branch 17 (.leaf (-12)) (.leaf (-11)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_063_1229 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (6))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (5)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1229
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-4)) (.leaf (-5)))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 27 (.leaf (-10)) (.leaf (-5))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.leaf (-1)) (.leaf (0))),
  (.branch 24 (.branch 4 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-15)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 18 (.leaf (-5)) (.leaf (-3))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_063_1230 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (6)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (5)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1230
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-18))) (.branch 15 (.leaf (-19)) (.branch 25 (.leaf (-20)) (.leaf (-25))))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 26 (.leaf (-25)) (.branch 27 (.leaf (-18)) (.leaf (-11)))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 23 (.branch 22 (.leaf (-3)) (.leaf (-2))) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_063 : Fin 35 → CycleWitness 7 := ![witnessD7_063_1196, witnessD7_063_1197, witnessD7_063_1198, witnessD7_063_1199, witnessD7_063_1200, witnessD7_063_1201, witnessD7_063_1202, witnessD7_063_1203, witnessD7_063_1204, witnessD7_063_1205, witnessD7_063_1206, witnessD7_063_1207, witnessD7_063_1208, witnessD7_063_1209, witnessD7_063_1210, witnessD7_063_1211, witnessD7_063_1212, witnessD7_063_1213, witnessD7_063_1214, witnessD7_063_1215, witnessD7_063_1216, witnessD7_063_1217, witnessD7_063_1218, witnessD7_063_1219, witnessD7_063_1220, witnessD7_063_1221, witnessD7_063_1222, witnessD7_063_1223, witnessD7_063_1224, witnessD7_063_1225, witnessD7_063_1226, witnessD7_063_1227, witnessD7_063_1228, witnessD7_063_1229, witnessD7_063_1230]
end RealPinwheel.FiveSixths


