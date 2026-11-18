-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_058
-- name    : RealPinwheel_FiveSixths_WitnessD7_058
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:04:24.496566+00:00
-- url     : https://prove2.me/theorems/0fe26abb-8fb8-4611-a060-75aae0edbc17
-- title:
--   Exact witness block D7_058
-- statement:
--   These exact witnesses represent words 1033 through 1063 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 1033–1063; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_058_1032 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (0))) (.branch 23 (.leaf (4)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1032
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 20 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 29 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 31 (.leaf (13)) (.leaf (14)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-23))),
  (.branch 25 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 18 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7)))),
  (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 20 (.branch 14 (.branch 11 (.branch 10 (.leaf (-23)) (.leaf (-22))) (.branch 12 (.leaf (-21)) (.branch 13 (.leaf (-20)) (.leaf (-19))))) (.branch 17 (.branch 15 (.leaf (-18)) (.branch 16 (.leaf (-17)) (.leaf (-16)))) (.branch 18 (.leaf (-15)) (.branch 19 (.leaf (-14)) (.leaf (-13)))))) (.branch 26 (.branch 23 (.branch 21 (.leaf (-12)) (.branch 22 (.leaf (-11)) (.leaf (-10)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_058_1033 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1033
  counts := ![(.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 28 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 13 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 16 (.leaf (0)) (.leaf (-16))),
  (.leaf (0))]
  high := ![(.branch 26 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-3)))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-13)))) (.branch 22 (.branch 21 (.leaf (-12)) (.leaf (-11))) (.branch 23 (.leaf (-10)) (.leaf (-9))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_058_1034 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1034
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.branch 10 (.leaf (-13)) (.leaf (-14))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 22 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 19 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-21))),
  (.branch 27 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 27 (.leaf (-14)) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.branch 29 (.branch 23 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-8)) (.branch 31 (.leaf (-6)) (.leaf (-4))))),
  (.branch 20 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-21)) (.leaf (-20))) (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17))))) (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_058_1035 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1035
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.leaf (-13)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 18 (.leaf (-5)) (.branch 31 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-17)) (.leaf (-18)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 24 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-24)))]
  high := ![(.branch 24 (.leaf (-13)) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (-7)),
  (.branch 29 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-15)) (.leaf (-12)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-6)) (.leaf (-3))))),
  (.branch 11 (.leaf (-2)) (.branch 22 (.leaf (-1)) (.leaf (0)))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.branch 14 (.branch 11 (.branch 9 (.leaf (-24)) (.branch 10 (.leaf (-23)) (.leaf (-22)))) (.branch 12 (.leaf (-21)) (.branch 13 (.leaf (-20)) (.leaf (-19))))) (.branch 17 (.branch 15 (.leaf (-18)) (.branch 16 (.leaf (-17)) (.leaf (-16)))) (.branch 18 (.leaf (-15)) (.branch 19 (.leaf (-14)) (.leaf (-13)))))) (.branch 26 (.branch 23 (.branch 21 (.leaf (-12)) (.branch 22 (.leaf (-11)) (.leaf (-10)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_058_1036 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (6)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (1))) (.branch 23 (.leaf (6)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (5)) (.leaf (4)))))))
  code := certificateD7_1036
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-17)) (.leaf (-18)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 21 (.leaf (-12)) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-15)) (.leaf (-12)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-6)) (.leaf (-3))))),
  (.branch 11 (.leaf (-2)) (.branch 22 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_058_1037 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (6)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1037
  counts := ![(.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 28 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-19))),
  (.branch 29 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 26 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-3)))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-19)) (.leaf (-18))) (.branch 16 (.leaf (-17)) (.leaf (-16)))) (.branch 19 (.branch 18 (.leaf (-15)) (.leaf (-14))) (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_058_1038 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1038
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.branch 10 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 15 (.leaf (0)) (.leaf (-17))),
  (.branch 31 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 27 (.leaf (-14)) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (-17)) (.leaf (-16))) (.branch 18 (.leaf (-15)) (.leaf (-14)))) (.branch 21 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 22 (.leaf (-11)) (.leaf (-10))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_058_1039 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1039
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-20))),
  (.branch 28 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 17 (.branch 14 (.branch 13 (.leaf (-20)) (.leaf (-19))) (.branch 15 (.leaf (-18)) (.branch 16 (.leaf (-17)) (.leaf (-16))))) (.branch 19 (.branch 18 (.leaf (-15)) (.leaf (-14))) (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_058_1040 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (3))) (.branch 31 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1040
  counts := ![(.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 28 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-27))),
  (.branch 21 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 18 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-3)))),
  (.branch 30 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 18 (.branch 11 (.branch 8 (.branch 6 (.leaf (-27)) (.branch 7 (.leaf (-26)) (.leaf (-25)))) (.branch 9 (.leaf (-24)) (.branch 10 (.leaf (-23)) (.leaf (-22))))) (.branch 14 (.branch 12 (.leaf (-21)) (.branch 13 (.leaf (-20)) (.leaf (-19)))) (.branch 16 (.branch 15 (.leaf (-18)) (.leaf (-17))) (.branch 17 (.leaf (-16)) (.leaf (-15)))))) (.branch 25 (.branch 21 (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))) (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_058_1041 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (6))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (2))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (6))) (.branch 31 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1041
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-8)) (.branch 20 (.leaf (-9)) (.leaf (-10))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-17)) (.leaf (-19)))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (-2)) (.leaf (-3)))),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 21 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-7)))),
  (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.branch 10 (.leaf (-19)) (.leaf (-18))) (.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.leaf (-3)) (.leaf (0))),
  (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_058_1042 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (2))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (3)) (.leaf (4)))))))
  code := certificateD7_1042
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-9)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 31 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-27))),
  (.branch 21 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 21 (.leaf (-12)) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.branch 30 (.branch 24 (.leaf (-11)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.branch 29 (.leaf (-9)) (.leaf (-7))) (.branch 31 (.leaf (-5)) (.leaf (-3)))),
  (.leaf (-3)),
  (.leaf (0)),
  (.branch 18 (.branch 11 (.branch 8 (.branch 6 (.leaf (-27)) (.branch 7 (.leaf (-26)) (.leaf (-25)))) (.branch 9 (.leaf (-24)) (.branch 10 (.leaf (-23)) (.leaf (-22))))) (.branch 14 (.branch 12 (.leaf (-21)) (.branch 13 (.leaf (-20)) (.leaf (-19)))) (.branch 16 (.branch 15 (.leaf (-18)) (.leaf (-17))) (.branch 17 (.leaf (-16)) (.leaf (-15)))))) (.branch 25 (.branch 21 (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))) (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_058_1043 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (5))) (.branch 15 (.leaf (3)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (1)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (4)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (6))) (.branch 31 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1043
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 19 (.leaf (-10)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-18))),
  (.branch 30 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.branch 31 (.leaf (-8)) (.leaf (-5))))),
  (.branch 23 (.branch 4 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.leaf (0)))),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 18 (.branch 16 (.branch 15 (.leaf (-18)) (.leaf (-17))) (.branch 17 (.leaf (-16)) (.leaf (-15)))) (.branch 20 (.branch 19 (.leaf (-14)) (.leaf (-13))) (.branch 21 (.leaf (-12)) (.branch 22 (.leaf (-11)) (.leaf (-10)))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_058_1044 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (5)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (4)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (4))) (.branch 23 (.leaf (1)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (6)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (4)) (.leaf (3)))))))
  code := certificateD7_1044
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-21))),
  (.branch 27 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 25 (.leaf (-8)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 27 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 28 (.leaf (-1)) (.leaf (0)))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-21)) (.leaf (-20))) (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17))))) (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_058_1045 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (3))) (.branch 23 (.leaf (1)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1045
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-28))),
  (.branch 20 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.leaf (-8)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 11 (.branch 7 (.branch 5 (.leaf (-28)) (.branch 6 (.leaf (-27)) (.leaf (-26)))) (.branch 9 (.branch 8 (.leaf (-25)) (.leaf (-24))) (.branch 10 (.leaf (-23)) (.leaf (-22))))) (.branch 14 (.branch 12 (.leaf (-21)) (.branch 13 (.leaf (-20)) (.leaf (-19)))) (.branch 16 (.branch 15 (.leaf (-18)) (.leaf (-17))) (.branch 17 (.leaf (-16)) (.leaf (-15)))))) (.branch 25 (.branch 21 (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))) (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 23 (.branch 21 (.leaf (-12)) (.branch 22 (.leaf (-11)) (.leaf (-10)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_058_1046 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (6)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (4)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (4)) (.leaf (3)))))))
  code := certificateD7_1046
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 28 (.leaf (-19)) (.leaf (-20)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 22 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-15))) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.branch 13 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 26 (.branch 23 (.branch 21 (.leaf (-12)) (.branch 22 (.leaf (-11)) (.leaf (-10)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_058_1047 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (6)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (5)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1047
  counts := ![(.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 28 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 8 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-29))),
  (.branch 19 (.leaf (0)) (.leaf (-13))),
  (.branch 27 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-21)))]
  high := ![(.branch 26 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-3)))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 17 (.branch 10 (.branch 6 (.branch 4 (.leaf (-29)) (.branch 5 (.leaf (-28)) (.leaf (-27)))) (.branch 8 (.branch 7 (.leaf (-26)) (.leaf (-25))) (.branch 9 (.leaf (-24)) (.leaf (-23))))) (.branch 13 (.branch 11 (.leaf (-22)) (.branch 12 (.leaf (-21)) (.leaf (-20)))) (.branch 15 (.branch 14 (.leaf (-19)) (.leaf (-18))) (.branch 16 (.leaf (-17)) (.leaf (-16)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (-15)) (.branch 19 (.leaf (-14)) (.leaf (-13)))) (.branch 22 (.branch 21 (.leaf (-12)) (.leaf (-11))) (.branch 23 (.leaf (-10)) (.leaf (-9))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 22 (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))) (.branch 23 (.leaf (-10)) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-21)) (.leaf (-20))) (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17))))) (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_058_1048 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (5))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (4)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (4))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (6))) (.branch 27 (.leaf (3)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1048
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-18))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-22))),
  (.branch 26 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 30 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 26 (.branch 3 (.leaf (-18)) (.leaf (-17))) (.branch 31 (.leaf (-14)) (.leaf (-7)))),
  (.branch 19 (.leaf (-2)) (.leaf (0))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 21 (.branch 15 (.branch 12 (.branch 11 (.leaf (-22)) (.leaf (-21))) (.branch 13 (.leaf (-20)) (.branch 14 (.leaf (-19)) (.leaf (-18))))) (.branch 18 (.branch 16 (.leaf (-17)) (.branch 17 (.leaf (-16)) (.leaf (-15)))) (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_058_1049 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (6)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (3))) (.branch 23 (.leaf (5)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1049
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-8)))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 31 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-17)) (.leaf (-18)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 23 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-25)))]
  high := ![(.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-4)))),
  (.leaf (-4)),
  (.branch 30 (.branch 23 (.leaf (-18)) (.leaf (-15))) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.branch 7 (.leaf (-2)) (.branch 20 (.leaf (-1)) (.leaf (0)))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 13 (.branch 10 (.branch 8 (.leaf (-25)) (.branch 9 (.leaf (-24)) (.leaf (-23)))) (.branch 11 (.leaf (-22)) (.branch 12 (.leaf (-21)) (.leaf (-20))))) (.branch 16 (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17)))) (.branch 17 (.leaf (-16)) (.branch 18 (.leaf (-15)) (.leaf (-14)))))) (.branch 25 (.branch 22 (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))) (.branch 23 (.leaf (-10)) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_058_1050 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (5)))))))
  code := certificateD7_1050
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-17)) (.leaf (-18)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 24 (.leaf (-13)) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.branch 30 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 29 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-15)) (.leaf (-12)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-6)) (.leaf (-3))))),
  (.branch 11 (.leaf (-2)) (.branch 22 (.leaf (-1)) (.leaf (0)))),
  (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_058_1051 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (6))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (5)))))))
  code := certificateD7_1051
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.branch 10 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.leaf (-22))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-2))) (.branch 18 (.leaf (-4)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 27 (.leaf (-14)) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.branch 29 (.branch 3 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-10)) (.leaf (-5))))),
  (.branch 19 (.leaf (-6)) (.leaf (-5))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_058_1052 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (3)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (4)) (.leaf (6))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (5)))))))
  code := certificateD7_1052
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-18))) (.branch 15 (.leaf (-22)) (.leaf (-23)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 22 (.leaf (-5)) (.branch 31 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 22 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 16 (.leaf (-23)) (.leaf (-21))) (.branch 31 (.leaf (-14)) (.leaf (-7)))),
  (.leaf (-7)),
  (.branch 29 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_058_1053 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (3)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1053
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 9 (.leaf (-13)) (.branch 18 (.leaf (-15)) (.leaf (-16))))),
  (.branch 2 (.leaf (0)) (.branch 25 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 29 (.branch 19 (.leaf (-16)) (.branch 24 (.leaf (-15)) (.leaf (-14)))) (.branch 30 (.leaf (-11)) (.branch 31 (.leaf (-8)) (.leaf (-5))))),
  (.branch 26 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-5)))),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_058_1054 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (5)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (6))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (4)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (5)))))))
  code := certificateD7_1054
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 26 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 24 (.leaf (-11)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 29 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 6 (.leaf (-17)) (.branch 17 (.leaf (-16)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.leaf (-1)) (.leaf (0))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_058_1055 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (6)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (4))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (5)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (1))) (.branch 23 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (1))) (.branch 27 (.leaf (6)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (5))) (.branch 31 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1055
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (-5)) (.leaf (-7)))),
  (.branch 11 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 15 (.branch 4 (.leaf (-23)) (.leaf (-22))) (.branch 26 (.leaf (-21)) (.leaf (-18)))) (.branch 29 (.branch 28 (.leaf (-15)) (.leaf (-12))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 20 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_058_1056 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (2))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (3)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (4))) (.branch 23 (.leaf (2)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1056
  counts := ![(.branch 15 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 28 (.leaf (9)) (.branch 30 (.leaf (10)) (.leaf (11)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-17)) (.leaf (-18)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-11)) (.leaf (-20))))]
  high := ![(.branch 31 (.leaf (-3)) (.leaf (-2))),
  (.branch 29 (.branch 19 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 25 (.leaf (-3)) (.leaf (-2))) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))),
  (.branch 29 (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-15)) (.leaf (-12)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.branch 23 (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18)))) (.branch 24 (.leaf (-17)) (.branch 25 (.leaf (-16)) (.leaf (-15))))) (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 30 (.leaf (-11)) (.branch 31 (.leaf (-10)) (.leaf (-9))))))]
def witnessD7_058_1057 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (6)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (5)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (1))) (.branch 31 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1057
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 9 (.leaf (-13)) (.branch 18 (.leaf (-15)) (.leaf (-16))))),
  (.branch 2 (.leaf (0)) (.branch 25 (.leaf (-8)) (.leaf (-9)))),
  (.branch 10 (.leaf (0)) (.branch 26 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-23)) (.leaf (-25)))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (-8)) (.leaf (-9)))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 29 (.branch 19 (.leaf (-16)) (.branch 24 (.leaf (-15)) (.leaf (-14)))) (.branch 30 (.leaf (-11)) (.branch 31 (.leaf (-8)) (.leaf (-5))))),
  (.branch 26 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-5)))),
  (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-1)) (.leaf (0)))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 25 (.branch 14 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-21)) (.leaf (-18)))) (.branch 29 (.branch 28 (.leaf (-15)) (.leaf (-12))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-1))]
def witnessD7_058_1058 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (4))) (.branch 15 (.leaf (1)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (5)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (4)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 31 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1058
  counts := ![(.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 27 (.leaf (-24)) (.leaf (-25)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0))]
  high := ![(.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-20))) (.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-10)) (.leaf (-5))))),
  (.branch 12 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-5)))),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_058_1059 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (5))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (4))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (5)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (6)) (.leaf (3))) (.branch 31 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1059
  counts := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 27 (.leaf (-24)) (.leaf (-25)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-8)) (.leaf (-13)))),
  (.branch 25 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 29 (.branch 23 (.leaf (-14)) (.leaf (-12))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-6)) (.leaf (-3))))),
  (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-20))) (.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-10)) (.leaf (-5))))),
  (.branch 12 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-5)))),
  (.branch 17 (.branch 10 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.branch 31 (.leaf (-10)) (.leaf (-7))))),
  (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-2)) (.leaf (0)))),
  (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_058_1060 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (5)) (.leaf (3)))))))
  code := certificateD7_1060
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 27 (.branch 24 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (-20)) (.leaf (-21)))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 28 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 28 (.branch 26 (.leaf (-21)) (.branch 27 (.leaf (-18)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3))))),
  (.branch 10 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (-3)))),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_058_1061 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (6))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (6))) (.branch 31 (.leaf (1)) (.leaf (5)))))))
  code := certificateD7_1061
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 19 (.leaf (-26)) (.branch 28 (.leaf (-27)) (.leaf (-28))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (-6)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-21))) (.branch 31 (.leaf (-14)) (.leaf (-7)))),
  (.branch 13 (.leaf (-12)) (.branch 27 (.leaf (-10)) (.leaf (-7)))),
  (.branch 30 (.branch 24 (.leaf (-11)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 26 (.leaf (-8)) (.branch 27 (.leaf (-7)) (.leaf (-6)))) (.branch 30 (.branch 29 (.leaf (-5)) (.leaf (-4))) (.branch 31 (.leaf (-3)) (.leaf (-2))))),
  (.branch 10 (.leaf (-2)) (.branch 22 (.leaf (-1)) (.leaf (0)))),
  (.branch 31 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_058_1062 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (6))) (.branch 15 (.leaf (0)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (6))) (.branch 31 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1062
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 19 (.leaf (-26)) (.leaf (-27)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 25 (.branch 20 (.leaf (-27)) (.leaf (-24))) (.branch 30 (.leaf (-21)) (.branch 31 (.leaf (-14)) (.leaf (-7))))),
  (.branch 4 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-7)))),
  (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 22 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.branch 23 (.branch 21 (.leaf (-12)) (.branch 22 (.leaf (-11)) (.leaf (-10)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_058 : Fin 31 → CycleWitness 7 := ![witnessD7_058_1032, witnessD7_058_1033, witnessD7_058_1034, witnessD7_058_1035, witnessD7_058_1036, witnessD7_058_1037, witnessD7_058_1038, witnessD7_058_1039, witnessD7_058_1040, witnessD7_058_1041, witnessD7_058_1042, witnessD7_058_1043, witnessD7_058_1044, witnessD7_058_1045, witnessD7_058_1046, witnessD7_058_1047, witnessD7_058_1048, witnessD7_058_1049, witnessD7_058_1050, witnessD7_058_1051, witnessD7_058_1052, witnessD7_058_1053, witnessD7_058_1054, witnessD7_058_1055, witnessD7_058_1056, witnessD7_058_1057, witnessD7_058_1058, witnessD7_058_1059, witnessD7_058_1060, witnessD7_058_1061, witnessD7_058_1062]
end RealPinwheel.FiveSixths


