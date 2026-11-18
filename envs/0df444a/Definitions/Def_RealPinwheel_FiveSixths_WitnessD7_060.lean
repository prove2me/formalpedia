-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_060
-- name    : RealPinwheel_FiveSixths_WitnessD7_060
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:05:50.219081+00:00
-- url     : https://prove2.me/theorems/6c8fbd6e-d25b-437c-a540-d4188ebfd25c
-- title:
--   Exact witness block D7_060
-- statement:
--   These exact witnesses represent words 1096 through 1128 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 1096–1128; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_060_1095 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (6))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1095
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 26 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 12 (.leaf (-3)) (.branch 27 (.leaf (-6)) (.leaf (-9))))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 22 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 21 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 18 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7)))),
  (.branch 22 (.branch 18 (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))) (.branch 20 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.leaf (-9))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-23)) (.leaf (-22))) (.branch 10 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19))))) (.branch 15 (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_060_1096 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (3))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (6))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1096
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 26 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-10)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (-2))) (.branch 27 (.leaf (-3)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 22 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 21 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 18 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 26 (.branch 13 (.leaf (-10)) (.branch 25 (.leaf (-9)) (.leaf (-8)))) (.branch 28 (.branch 27 (.leaf (-7)) (.leaf (-6))) (.branch 29 (.leaf (-5)) (.leaf (-4))))),
  (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-5)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-23)) (.leaf (-22))) (.branch 10 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19))))) (.branch 15 (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_060_1097 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (5)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (6)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1097
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 20 (.leaf (9)) (.leaf (10)))) (.branch 27 (.branch 24 (.leaf (11)) (.leaf (12))) (.branch 29 (.leaf (13)) (.leaf (14)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-8)) (.leaf (-9)))) (.branch 7 (.leaf (-10)) (.branch 9 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 25 (.leaf (-12)) (.leaf (-7))),
  (.branch 18 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 20 (.branch 15 (.branch 12 (.branch 11 (.leaf (-20)) (.leaf (-19))) (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16))))) (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_060_1098 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (4)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (6)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1098
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 20 (.leaf (9)) (.leaf (10)))) (.branch 27 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 29 (.leaf (13)) (.leaf (14)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 5 (.leaf (-9)) (.branch 7 (.leaf (-10)) (.leaf (-11))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-22))),
  (.branch 23 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 23 (.leaf (-11)) (.leaf (-7))),
  (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-10)) (.leaf (-8)))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 20 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-3)))),
  (.branch 27 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 19 (.branch 13 (.branch 10 (.branch 9 (.leaf (-22)) (.leaf (-21))) (.branch 11 (.leaf (-20)) (.branch 12 (.leaf (-19)) (.leaf (-18))))) (.branch 16 (.branch 14 (.leaf (-17)) (.branch 15 (.leaf (-16)) (.leaf (-15)))) (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_060_1099 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (0)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (6)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1099
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 25 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-19))),
  (.branch 26 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 26 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.leaf (-1)) (.leaf (0))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 20 (.branch 15 (.branch 13 (.branch 12 (.leaf (-19)) (.leaf (-18))) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_060_1100 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (2)))))) (.branch 23 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (0))) (.branch 22 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (2)))))))
  code := certificateD7_1100
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 25 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 17 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 22 (.leaf (-11)) (.leaf (-16)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-26))),
  (.branch 19 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-18))),
  (.branch 27 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 26 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.leaf (-16)) (.leaf (-14))),
  (.branch 16 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.branch 10 (.branch 7 (.branch 5 (.leaf (-26)) (.branch 6 (.leaf (-25)) (.leaf (-24)))) (.branch 8 (.leaf (-23)) (.branch 9 (.leaf (-22)) (.leaf (-21))))) (.branch 13 (.branch 11 (.leaf (-20)) (.branch 12 (.leaf (-19)) (.leaf (-18)))) (.branch 15 (.branch 14 (.leaf (-17)) (.leaf (-16))) (.branch 16 (.leaf (-15)) (.leaf (-14)))))) (.branch 23 (.branch 20 (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.branch 16 (.branch 14 (.branch 13 (.leaf (-18)) (.leaf (-17))) (.branch 15 (.leaf (-16)) (.leaf (-15)))) (.branch 18 (.branch 17 (.leaf (-14)) (.leaf (-13))) (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_060_1101 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (5)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (6)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1101
  counts := ![(.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 16 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 28 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 25 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 28 (.branch 20 (.leaf (-7)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 20 (.branch 15 (.branch 12 (.branch 11 (.leaf (-20)) (.leaf (-19))) (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16))))) (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_060_1102 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (5))) (.branch 10 (.leaf (0)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (6))) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1102
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 16 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 17 (.leaf (-7)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-21))),
  (.branch 24 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.leaf (-10)) (.branch 24 (.leaf (-9)) (.leaf (-8)))),
  (.branch 21 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-21)) (.leaf (-20))) (.branch 12 (.leaf (-19)) (.branch 13 (.leaf (-18)) (.leaf (-17))))) (.branch 16 (.branch 15 (.leaf (-16)) (.leaf (-15))) (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_060_1103 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (4)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (5))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1103
  counts := ![(.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 16 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 28 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 25 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 28 (.branch 20 (.leaf (-7)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_060_1104 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1104
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 11 (.leaf (-27)) (.leaf (-29)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-4)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-11)) (.leaf (-15)))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 23 (.branch 12 (.leaf (-29)) (.leaf (-28))) (.branch 26 (.leaf (-25)) (.branch 29 (.leaf (-22)) (.leaf (-11))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))),
  (.branch 28 (.branch 27 (.leaf (-6)) (.leaf (-5))) (.branch 29 (.leaf (-4)) (.leaf (-3)))),
  (.branch 27 (.branch 25 (.leaf (-15)) (.branch 26 (.leaf (-13)) (.leaf (-11)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-7)) (.leaf (-5))))),
  (.branch 22 (.branch 18 (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))) (.branch 20 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.leaf (-9))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_060_1105 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (4))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (6))) (.branch 21 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1105
  counts := ![(.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 26 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 29 (.leaf (-4)) (.leaf (-2))),
  (.branch 27 (.branch 18 (.leaf (-11)) (.branch 26 (.leaf (-10)) (.leaf (-8)))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_060_1106 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (5))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (6)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1106
  counts := ![(.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 26 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 29 (.leaf (-4)) (.leaf (-2))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_060_1107 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (6))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1107
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 20 (.leaf (9)) (.leaf (10)))) (.branch 27 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 29 (.leaf (13)) (.leaf (14)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 5 (.leaf (-9)) (.branch 7 (.leaf (-10)) (.leaf (-11))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 23 (.leaf (-11)) (.leaf (-7))),
  (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-10)) (.leaf (-8)))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 27 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_060_1108 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (6)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (6)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1108
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 11 (.leaf (-27)) (.leaf (-29)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-11)) (.leaf (-15)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 23 (.branch 12 (.leaf (-29)) (.leaf (-28))) (.branch 26 (.leaf (-25)) (.branch 29 (.leaf (-22)) (.leaf (-11))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))),
  (.branch 27 (.branch 25 (.leaf (-15)) (.branch 26 (.leaf (-13)) (.leaf (-11)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-7)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_060_1109 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (1))) (.branch 10 (.leaf (4)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (5))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1109
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))),
  (.branch 15 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-20))),
  (.branch 20 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-6)) (.leaf (-3)))),
  (.branch 26 (.leaf (-5)) (.leaf (-3))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.branch 15 (.branch 12 (.branch 11 (.leaf (-20)) (.leaf (-19))) (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16))))) (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_060_1110 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (4)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (3)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (5)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (4)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1110
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-16))),
  (.branch 29 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 24 (.branch 20 (.leaf (-14)) (.leaf (-13))) (.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-8)) (.leaf (-4))))),
  (.branch 25 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.leaf (-4)))),
  (.branch 23 (.branch 19 (.leaf (-3)) (.leaf (-2))) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 18 (.branch 16 (.branch 15 (.leaf (-16)) (.leaf (-15))) (.branch 17 (.leaf (-14)) (.leaf (-13)))) (.branch 20 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.leaf (-9))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_060_1111 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (6)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1111
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 28 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-24))),
  (.branch 21 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 27 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 12 (.branch 9 (.branch 7 (.leaf (-24)) (.branch 8 (.leaf (-23)) (.leaf (-22)))) (.branch 10 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19))))) (.branch 15 (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_060_1112 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (3))) (.branch 29 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1112
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 26 (.branch 24 (.leaf (9)) (.leaf (10))) (.branch 29 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 27 (.leaf (-3)) (.leaf (-2))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.branch 26 (.leaf (-10)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 21 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 18 (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))) (.branch 20 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.leaf (-9))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_060_1113 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1113
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.leaf (-4)) (.leaf (-3))),
  (.branch 27 (.branch 26 (.leaf (-10)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 21 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 18 (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))) (.branch 20 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.leaf (-9))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_060_1114 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (2))) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1114
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 28 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 18 (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))) (.branch 20 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.leaf (-9))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_060_1115 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (4))) (.branch 10 (.leaf (2)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (4)) (.leaf (6)))))))
  code := certificateD7_1115
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-6)) (.leaf (-3)))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.branch 26 (.leaf (-10)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 21 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1)),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_060_1116 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (4)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (4))) (.branch 21 (.leaf (1)) (.leaf (6))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1116
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 22 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-4)))),
  (.branch 28 (.branch 19 (.leaf (-6)) (.leaf (-5))) (.branch 29 (.leaf (-4)) (.leaf (-3)))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-23)) (.leaf (-22))) (.branch 10 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19))))) (.branch 15 (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_060_1117 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (1)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (4))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (6)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1117
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-19))),
  (.branch 26 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 18 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 15 (.branch 13 (.branch 12 (.leaf (-19)) (.leaf (-18))) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_060_1118 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (1)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (5))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (6)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1118
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 18 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_060_1119 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (1)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (6))) (.branch 21 (.leaf (1)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1119
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-25))),
  (.branch 20 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 24 (.branch 20 (.leaf (-14)) (.leaf (-13))) (.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-8)) (.leaf (-4))))),
  (.branch 22 (.branch 18 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 27 (.branch 16 (.leaf (-12)) (.leaf (-11))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-7)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 17 (.branch 11 (.branch 8 (.branch 6 (.leaf (-25)) (.branch 7 (.leaf (-24)) (.leaf (-23)))) (.branch 9 (.leaf (-22)) (.branch 10 (.leaf (-21)) (.leaf (-20))))) (.branch 14 (.branch 12 (.leaf (-19)) (.branch 13 (.leaf (-18)) (.leaf (-17)))) (.branch 15 (.leaf (-16)) (.branch 16 (.leaf (-15)) (.leaf (-14)))))) (.branch 23 (.branch 20 (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_060_1120 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (6))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (5))) (.branch 14 (.leaf (0)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (6))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1120
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.leaf (-4)) (.leaf (-3))),
  (.branch 27 (.branch 26 (.leaf (-10)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_060_1121 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (1)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (6))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1121
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.branch 14 (.leaf (-9)) (.leaf (-10))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 29 (.leaf (-4)) (.leaf (-5)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 18 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 22 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-8)) (.leaf (-4)))),
  (.branch 24 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-7)) (.leaf (-4)))),
  (.leaf (-5)),
  (.branch 27 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-23)) (.leaf (-22))) (.branch 10 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19))))) (.branch 15 (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_060_1122 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (4))) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (3)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (6))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (4)) (.leaf (5)))))))
  code := certificateD7_1122
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-11)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 28 (.branch 24 (.leaf (-13)) (.leaf (-12))) (.branch 29 (.leaf (-8)) (.leaf (-4)))),
  (.branch 29 (.leaf (-8)) (.leaf (-4))),
  (.branch 27 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_060_1123 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (3))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (4))) (.branch 14 (.leaf (2)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (3))) (.branch 25 (.leaf (6)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (4))) (.branch 29 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1123
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.leaf (-1)) (.leaf (0))),
  (.branch 21 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 20 (.branch 15 (.branch 12 (.branch 11 (.leaf (-20)) (.leaf (-19))) (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16))))) (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_060_1124 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (0)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (5)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1124
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 16 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 26 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-19)))]
  high := ![(.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 23 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.branch 15 (.branch 13 (.branch 12 (.leaf (-19)) (.leaf (-18))) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_060_1125 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (6)) (.leaf (0))) (.branch 10 (.leaf (5)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (6)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (5)))))))
  code := certificateD7_1125
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 21 (.branch 17 (.leaf (-11)) (.leaf (-10))) (.branch 25 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-4))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.branch 27 (.branch 5 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_060_1126 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (6))) (.branch 10 (.leaf (2)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (6))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (5))) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (4))) (.branch 29 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1126
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.branch 26 (.leaf (-10)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 20 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-3)))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_060_1127 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (1)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (6)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1127
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-26))),
  (.branch 19 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-8)) (.leaf (-4)))),
  (.branch 22 (.branch 18 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 10 (.branch 7 (.branch 5 (.leaf (-26)) (.branch 6 (.leaf (-25)) (.leaf (-24)))) (.branch 8 (.leaf (-23)) (.branch 9 (.leaf (-22)) (.leaf (-21))))) (.branch 13 (.branch 11 (.leaf (-20)) (.branch 12 (.leaf (-19)) (.leaf (-18)))) (.branch 15 (.branch 14 (.leaf (-17)) (.leaf (-16))) (.branch 16 (.leaf (-15)) (.leaf (-14)))))) (.branch 23 (.branch 20 (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_060 : Fin 33 → CycleWitness 7 := ![witnessD7_060_1095, witnessD7_060_1096, witnessD7_060_1097, witnessD7_060_1098, witnessD7_060_1099, witnessD7_060_1100, witnessD7_060_1101, witnessD7_060_1102, witnessD7_060_1103, witnessD7_060_1104, witnessD7_060_1105, witnessD7_060_1106, witnessD7_060_1107, witnessD7_060_1108, witnessD7_060_1109, witnessD7_060_1110, witnessD7_060_1111, witnessD7_060_1112, witnessD7_060_1113, witnessD7_060_1114, witnessD7_060_1115, witnessD7_060_1116, witnessD7_060_1117, witnessD7_060_1118, witnessD7_060_1119, witnessD7_060_1120, witnessD7_060_1121, witnessD7_060_1122, witnessD7_060_1123, witnessD7_060_1124, witnessD7_060_1125, witnessD7_060_1126, witnessD7_060_1127]
end RealPinwheel.FiveSixths


