-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_005
-- name    : RealPinwheel_FiveSixths_WitnessD6_005
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:15:54.998207+00:00
-- url     : https://prove2.me/theorems/425f1c1e-bf0a-41e7-bdd1-ba0fbf6e4958
-- title:
--   Exact witness block D6_005
-- statement:
--   These exact witnesses represent words 106 through 132 of source certificate file D6. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D6, entries 106–132; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D6.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD6
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD6_005_105 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (3))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (3))) (.branch 30 (.leaf (0)) (.leaf (5)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (4))))))))
  code := certificateD6_105
  counts := ![(.branch 17 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 22 (.leaf (11)) (.branch 24 (.leaf (12)) (.leaf (13))))) (.branch 30 (.branch 28 (.leaf (14)) (.leaf (15))) (.branch 32 (.leaf (16)) (.branch 35 (.leaf (17)) (.leaf (18))))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 33 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_005_106 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (4)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (4))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (4)) (.leaf (0))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (5)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (4))))))))
  code := certificateD6_106
  counts := ![(.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 25 (.branch 20 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 22 (.leaf (10)) (.leaf (11)))) (.branch 29 (.branch 27 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 34 (.leaf (15)) (.leaf (16))))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))) (.branch 20 (.leaf (-9)) (.branch 22 (.leaf (-10)) (.leaf (-11))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-21)) (.leaf (-22)))) (.branch 24 (.leaf (-23)) (.branch 31 (.leaf (-24)) (.leaf (-25))))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 30 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 33 (.branch 32 (.leaf (-25)) (.leaf (-20))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-10)) (.leaf (-5))))),
  (.branch 14 (.leaf (-7)) (.leaf (-5))),
  (.branch 34 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_005_107 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (1))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (3))) (.branch 26 (.leaf (0)) (.leaf (2))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (5)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (1))))))))
  code := certificateD6_107
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 23 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 20 (.leaf (-10)) (.leaf (-12)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 24 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.leaf (0)) (.leaf (-24))),
  (.branch 30 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 32 (.branch 21 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 29 (.branch 25 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.leaf (0)))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 24 (.branch 18 (.branch 15 (.branch 13 (.leaf (-24)) (.branch 14 (.leaf (-23)) (.leaf (-22)))) (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19))))) (.branch 21 (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16)))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_005_108 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (4))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (2))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (5))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1))))))))
  code := certificateD6_108
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 23 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 28 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 20 (.leaf (-10)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 30 (.leaf (-6)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-21))),
  (.branch 33 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 32 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 22 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (0)))),
  (.branch 31 (.leaf (-8)) (.leaf (-7))),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 20 (.branch 17 (.branch 16 (.leaf (-21)) (.leaf (-20))) (.branch 18 (.leaf (-19)) (.branch 19 (.leaf (-18)) (.leaf (-17))))) (.branch 22 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_005_109 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (2))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (3))) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (5)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3))))))))
  code := certificateD6_109
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 23 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 28 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 20 (.leaf (-10)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-22))),
  (.branch 32 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 32 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 26 (.leaf (-4)) (.branch 31 (.leaf (-3)) (.leaf (-2)))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-22)) (.leaf (-21))) (.branch 17 (.leaf (-20)) (.branch 18 (.leaf (-19)) (.leaf (-18))))) (.branch 22 (.branch 20 (.leaf (-17)) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_005_110 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (2)) (.leaf (1))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (4)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (2)) (.leaf (1)))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (1))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (5)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (0))) (.branch 35 (.leaf (2)) (.leaf (1)))))))
  code := certificateD6_110
  counts := ![(.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 25 (.branch 20 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 23 (.leaf (10)) (.leaf (11)))) (.branch 29 (.branch 28 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 34 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 9 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))) (.branch 20 (.leaf (-9)) (.branch 29 (.leaf (-10)) (.leaf (-11))))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 13 (.leaf (0)) (.leaf (-23))),
  (.branch 31 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 30 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 18 (.branch 15 (.branch 14 (.leaf (-23)) (.leaf (-22))) (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19))))) (.branch 21 (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16)))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_005_111 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (4))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (5))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (2)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (3))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))))))
  code := certificateD6_111
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 23 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 20 (.leaf (-10)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (-6)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-27))),
  (.branch 27 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 32 (.branch 21 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 25 (.leaf (-6)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 34 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))),
  (.branch 22 (.branch 15 (.branch 12 (.branch 10 (.leaf (-27)) (.branch 11 (.leaf (-26)) (.leaf (-25)))) (.branch 13 (.leaf (-24)) (.branch 14 (.leaf (-23)) (.leaf (-22))))) (.branch 18 (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19)))) (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_005_112 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (4))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (3))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (5)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (4))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1))))))))
  code := certificateD6_112
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 23 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 20 (.leaf (-10)) (.leaf (-12)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 24 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 32 (.branch 21 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 29 (.branch 25 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.leaf (0)))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_005_113 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (1)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (4))) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (0))) (.branch 26 (.leaf (1)) (.leaf (0))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (5)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (1))))))))
  code := certificateD6_113
  counts := ![(.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 25 (.branch 20 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 23 (.leaf (10)) (.leaf (11)))) (.branch 30 (.branch 27 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 34 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 20 (.leaf (-18)) (.leaf (-20)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-7)) (.leaf (-9)))),
  (.branch 24 (.leaf (0)) (.branch 35 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 10 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 28 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 33 (.branch 18 (.leaf (-9)) (.branch 32 (.leaf (-8)) (.leaf (-7)))) (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-5)) (.leaf (-4))))),
  (.leaf (-4)),
  (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_005_114 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (5))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (4))))))))
  code := certificateD6_114
  counts := ![(.branch 16 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 25 (.branch 21 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 23 (.leaf (10)) (.leaf (11)))) (.branch 30 (.branch 28 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 34 (.leaf (15)) (.leaf (16))))))),
  (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 26 (.branch 22 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 24 (.leaf (10)) (.leaf (11)))) (.branch 31 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 33 (.leaf (14)) (.branch 35 (.leaf (15)) (.leaf (16))))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.branch 7 (.leaf (-7)) (.leaf (-8))))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-1))) (.branch 6 (.leaf (-2)) (.branch 8 (.leaf (-3)) (.leaf (-4))))),
  (.branch 9 (.leaf (0)) (.leaf (-27))),
  (.branch 27 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 18 (.leaf (0)) (.leaf (-18)))]
  high := ![(.branch 35 (.leaf (-8)) (.leaf (-4))),
  (.leaf (-4)),
  (.branch 22 (.branch 15 (.branch 12 (.branch 10 (.leaf (-27)) (.branch 11 (.leaf (-26)) (.leaf (-25)))) (.branch 13 (.leaf (-24)) (.branch 14 (.leaf (-23)) (.leaf (-22))))) (.branch 18 (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19)))) (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-14)) (.leaf (-13))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD6_005_115 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (2)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (5))))))))
  code := certificateD6_115
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 25 (.leaf (10)) (.leaf (11)))) (.branch 32 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 34 (.leaf (14)) (.leaf (15)))))),
  (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 23 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 35 (.leaf (14)) (.leaf (15)))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-24))),
  (.branch 24 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.branch 30 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (-5)),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 18 (.branch 15 (.branch 13 (.leaf (-24)) (.branch 14 (.leaf (-23)) (.leaf (-22)))) (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19))))) (.branch 21 (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16)))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_005_116 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (2))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (2)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (5))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))))))
  code := certificateD6_116
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 25 (.leaf (10)) (.leaf (11)))) (.branch 32 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 34 (.leaf (14)) (.leaf (15)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 26 (.branch 19 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-27))),
  (.branch 21 (.leaf (0)) (.leaf (-15))),
  (.branch 33 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 30 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 32 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 22 (.branch 15 (.branch 12 (.branch 10 (.leaf (-27)) (.branch 11 (.leaf (-26)) (.leaf (-25)))) (.branch 13 (.leaf (-24)) (.branch 14 (.leaf (-23)) (.leaf (-22))))) (.branch 18 (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19)))) (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_005_117 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (1)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (3)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3))))))))
  code := certificateD6_117
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 21 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 32 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 26 (.branch 20 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 18 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-29))),
  (.branch 25 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 22 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-7)))),
  (.branch 32 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.branch 33 (.leaf (-1)) (.leaf (0))))),
  (.branch 21 (.branch 14 (.branch 10 (.branch 8 (.leaf (-29)) (.branch 9 (.leaf (-28)) (.leaf (-27)))) (.branch 12 (.branch 11 (.leaf (-26)) (.leaf (-25))) (.branch 13 (.leaf (-24)) (.leaf (-23))))) (.branch 17 (.branch 15 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_005_118 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (0)) (.leaf (2))))))))
  code := certificateD6_118
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 23 (.leaf (10)) (.leaf (11)))) (.branch 30 (.branch 28 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 35 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-20))),
  (.branch 34 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 33 (.leaf (-7)) (.leaf (-4))),
  (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 21 (.branch 18 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16))))) (.branch 23 (.branch 22 (.leaf (-15)) (.leaf (-14))) (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))))) (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_005_119 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (0)) (.leaf (5)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (4))))))))
  code := certificateD6_119
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 23 (.leaf (10)) (.leaf (11)))) (.branch 30 (.branch 28 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 35 (.leaf (15)) (.leaf (16))))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (-6)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 33 (.leaf (-7)) (.leaf (-4))),
  (.branch 30 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 34 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))),
  (.branch 33 (.branch 19 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_005_120 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (5))))))))
  code := certificateD6_120
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 23 (.leaf (10)) (.leaf (11)))) (.branch 30 (.branch 28 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 35 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 31 (.leaf (-7)) (.leaf (-9)))),
  (.branch 18 (.leaf (0)) (.leaf (-18))),
  (.leaf (0))]
  high := ![(.branch 33 (.leaf (-7)) (.leaf (-4))),
  (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 28 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5))))),
  (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-14)) (.leaf (-13))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD6_005_121 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (3))) (.branch 30 (.leaf (0)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (5)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (2))))))))
  code := certificateD6_121
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 10 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-22))),
  (.branch 32 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 31 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.branch 29 (.leaf (-7)) (.leaf (-6))) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 27 (.leaf (-2)) (.branch 32 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-22)) (.leaf (-21))) (.branch 17 (.leaf (-20)) (.branch 18 (.leaf (-19)) (.leaf (-18))))) (.branch 22 (.branch 20 (.leaf (-17)) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_005_122 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (5)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))))))
  code := certificateD6_122
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-22))),
  (.branch 32 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 31 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.leaf (-9)) (.branch 32 (.leaf (-7)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-22)) (.leaf (-21))) (.branch 17 (.leaf (-20)) (.branch 18 (.leaf (-19)) (.leaf (-18))))) (.branch 22 (.branch 20 (.leaf (-17)) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_005_123 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (2)) (.leaf (5)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (3))) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (4)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3))))))))
  code := certificateD6_123
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 20 (.leaf (-8)) (.leaf (-10)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-16))) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 25 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 26 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.leaf (-7)))),
  (.branch 34 (.branch 19 (.leaf (-18)) (.leaf (-15))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_005_124 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (2)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (4)) (.leaf (0))) (.branch 30 (.leaf (3)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (3))))))))
  code := certificateD6_124
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 21 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 32 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-15)))),
  (.leaf (0)),
  (.branch 17 (.leaf (0)) (.branch 35 (.leaf (-3)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 22 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-7)))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 19 (.leaf (-15)) (.leaf (-13))) (.branch 35 (.leaf (-9)) (.leaf (-5)))),
  (.leaf (0)),
  (.leaf (-5)),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_005_125 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (5))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1))))))))
  code := certificateD6_125
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 26 (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 23 (.leaf (5)) (.leaf (6))) (.branch 30 (.leaf (7)) (.branch 35 (.leaf (8)) (.leaf (9)))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-27))),
  (.branch 21 (.leaf (0)) (.leaf (-15))),
  (.branch 33 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 33 (.leaf (-1)) (.leaf (0))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.branch 15 (.branch 12 (.branch 10 (.leaf (-27)) (.branch 11 (.leaf (-26)) (.leaf (-25)))) (.branch 13 (.leaf (-24)) (.branch 14 (.leaf (-23)) (.leaf (-22))))) (.branch 18 (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19)))) (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_005_126 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (5))) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (2))))))))
  code := certificateD6_126
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 5 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 21 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 23 (.leaf (-3)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-25))),
  (.branch 29 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 34 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 21 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-5)))),
  (.branch 33 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 23 (.branch 17 (.branch 14 (.branch 12 (.leaf (-25)) (.branch 13 (.leaf (-24)) (.leaf (-23)))) (.branch 15 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20))))) (.branch 20 (.branch 18 (.leaf (-19)) (.branch 19 (.leaf (-18)) (.leaf (-17)))) (.branch 21 (.leaf (-16)) (.branch 22 (.leaf (-15)) (.leaf (-14)))))) (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_005_127 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (0))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (1)) (.leaf (5))))))))
  code := certificateD6_127
  counts := ![(.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 29 (.leaf (-9)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 18 (.leaf (0)) (.leaf (-18))),
  (.leaf (0))]
  high := ![(.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.leaf (-9)) (.branch 32 (.leaf (-7)) (.leaf (-5)))),
  (.branch 30 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-14)) (.leaf (-13))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD6_005_128 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (5)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (3)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3))))))))
  code := certificateD6_128
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-28))),
  (.branch 26 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 21 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-5)))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 22 (.branch 15 (.branch 11 (.branch 9 (.leaf (-28)) (.branch 10 (.leaf (-27)) (.leaf (-26)))) (.branch 13 (.branch 12 (.leaf (-25)) (.leaf (-24))) (.branch 14 (.leaf (-23)) (.leaf (-22))))) (.branch 18 (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19)))) (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_005_129 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (2))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (1)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (4)) (.leaf (0))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (1)) (.leaf (3))))))))
  code := certificateD6_129
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 10 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.branch 20 (.leaf (-8)) (.leaf (-10)))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 18 (.leaf (-9)) (.branch 28 (.leaf (-10)) (.leaf (-12))))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (-2)) (.leaf (-3)))),
  (.branch 14 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 34 (.branch 30 (.leaf (-17)) (.leaf (-15))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 26 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.leaf (-7)))),
  (.branch 29 (.leaf (-12)) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 32 (.leaf (-3)) (.leaf (0))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_005_130 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (2)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (2)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (3))) (.branch 30 (.leaf (0)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (2)) (.leaf (1))))))))
  code := certificateD6_130
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 33 (.leaf (-10)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-29))),
  (.branch 25 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 34 (.leaf (-11)) (.branch 35 (.leaf (-8)) (.leaf (-5)))),
  (.branch 29 (.branch 21 (.leaf (-10)) (.branch 25 (.leaf (-9)) (.leaf (-8)))) (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-3)) (.leaf (0))))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 21 (.branch 14 (.branch 10 (.branch 8 (.leaf (-29)) (.branch 9 (.leaf (-28)) (.leaf (-27)))) (.branch 12 (.branch 11 (.leaf (-26)) (.leaf (-25))) (.branch 13 (.leaf (-24)) (.leaf (-23))))) (.branch 17 (.branch 15 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_005_131 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (5)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (1)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (2))))))))
  code := certificateD6_131
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 22 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 32 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 35 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 11 (.leaf (-12)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-28))),
  (.branch 26 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 30 (.leaf (-13)) (.branch 33 (.leaf (-10)) (.leaf (-7)))),
  (.branch 21 (.leaf (-5)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 33 (.branch 22 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 15 (.branch 11 (.branch 9 (.leaf (-28)) (.branch 10 (.leaf (-27)) (.leaf (-26)))) (.branch 13 (.branch 12 (.leaf (-25)) (.leaf (-24))) (.branch 14 (.leaf (-23)) (.leaf (-22))))) (.branch 18 (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19)))) (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_005 : Fin 27 → CycleWitness 6 := ![witnessD6_005_105, witnessD6_005_106, witnessD6_005_107, witnessD6_005_108, witnessD6_005_109, witnessD6_005_110, witnessD6_005_111, witnessD6_005_112, witnessD6_005_113, witnessD6_005_114, witnessD6_005_115, witnessD6_005_116, witnessD6_005_117, witnessD6_005_118, witnessD6_005_119, witnessD6_005_120, witnessD6_005_121, witnessD6_005_122, witnessD6_005_123, witnessD6_005_124, witnessD6_005_125, witnessD6_005_126, witnessD6_005_127, witnessD6_005_128, witnessD6_005_129, witnessD6_005_130, witnessD6_005_131]
end RealPinwheel.FiveSixths


