-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_062
-- name    : RealPinwheel_FiveSixths_WitnessD7_062
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:08:05.827807+00:00
-- url     : https://prove2.me/theorems/f2dbf43f-2d5d-4d4d-aab9-a3de404c84fd
-- title:
--   Exact witness block D7_062
-- statement:
--   These exact witnesses represent words 1162 through 1196 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 1162–1196; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_062_1161 : CycleWitness 7 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (6))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (3)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1161
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-14)) (.leaf (-18)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 13 (.leaf (-11)) (.leaf (-16))))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 19 (.leaf (-3)) (.leaf (-5)))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-22))),
  (.branch 21 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 5 (.leaf (-18)) (.branch 28 (.leaf (-17)) (.leaf (-12)))),
  (.branch 27 (.branch 14 (.leaf (-16)) (.leaf (-15))) (.branch 28 (.leaf (-11)) (.leaf (-7)))),
  (.leaf (-5)),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.leaf (-2)))),
  (.branch 15 (.leaf (-1)) (.leaf (0))),
  (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-22)) (.leaf (-21))) (.branch 10 (.leaf (-20)) (.branch 11 (.leaf (-19)) (.leaf (-18))))) (.branch 15 (.branch 13 (.leaf (-17)) (.branch 14 (.leaf (-16)) (.leaf (-15)))) (.branch 16 (.leaf (-14)) (.branch 17 (.leaf (-13)) (.leaf (-12)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-11)) (.leaf (-10))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-8)) (.leaf (-7))))) (.branch 26 (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-8)) (.leaf (-7))) (.branch 24 (.leaf (-6)) (.leaf (-5)))) (.branch 27 (.branch 26 (.leaf (-4)) (.leaf (-3))) (.branch 28 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_062_1162 : CycleWitness 7 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (6))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (2)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (1)) (.leaf (2)))))))
  code := certificateD7_1162
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 18 (.leaf (-10)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 28 (.leaf (-12)) (.leaf (-14)))),
  (.branch 14 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-20))),
  (.branch 9 (.leaf (0)) (.branch 17 (.leaf (-1)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-23))),
  (.branch 21 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 23 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-7)) (.leaf (-4))))),
  (.leaf (-14)),
  (.branch 20 (.branch 15 (.leaf (-3)) (.leaf (-2))) (.branch 25 (.leaf (-1)) (.leaf (0)))),
  (.branch 25 (.branch 14 (.branch 4 (.leaf (-20)) (.leaf (-19))) (.branch 24 (.leaf (-18)) (.leaf (-15)))) (.branch 27 (.branch 26 (.leaf (-12)) (.leaf (-9))) (.branch 28 (.leaf (-6)) (.leaf (-3))))),
  (.branch 28 (.leaf (-3)) (.leaf (-2))),
  (.branch 17 (.branch 11 (.branch 8 (.branch 7 (.leaf (-23)) (.leaf (-22))) (.branch 9 (.leaf (-21)) (.branch 10 (.leaf (-20)) (.leaf (-19))))) (.branch 14 (.branch 12 (.leaf (-18)) (.branch 13 (.leaf (-17)) (.leaf (-16)))) (.branch 15 (.leaf (-15)) (.branch 16 (.leaf (-14)) (.leaf (-13)))))) (.branch 23 (.branch 20 (.branch 18 (.leaf (-12)) (.branch 19 (.leaf (-11)) (.leaf (-10)))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-8)) (.leaf (-7))))) (.branch 26 (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-8)) (.leaf (-7))) (.branch 24 (.leaf (-6)) (.leaf (-5)))) (.branch 27 (.branch 26 (.leaf (-4)) (.leaf (-3))) (.branch 28 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_062_1163 : CycleWitness 7 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (4))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (6)) (.leaf (3))) (.branch 24 (.leaf (2)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (5))) (.branch 28 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1163
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-10)))) (.branch 12 (.leaf (-11)) (.branch 20 (.leaf (-12)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-21)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.branch 27 (.leaf (-1)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 26 (.branch 21 (.leaf (-14)) (.leaf (-13))) (.branch 27 (.leaf (-11)) (.branch 28 (.leaf (-9)) (.leaf (-7))))),
  (.branch 22 (.branch 12 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19)))) (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-12)) (.leaf (-6))))),
  (.leaf (-2)),
  (.branch 25 (.branch 14 (.branch 4 (.leaf (-20)) (.leaf (-19))) (.branch 24 (.leaf (-18)) (.leaf (-15)))) (.branch 27 (.branch 26 (.leaf (-12)) (.leaf (-9))) (.branch 28 (.leaf (-6)) (.leaf (-3))))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 28 (.leaf (-3)) (.leaf (-2))),
  (.branch 25 (.branch 23 (.branch 7 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.leaf (-2)))))]
def witnessD7_062_1164 : CycleWitness 7 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (6))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (2)))))))
  code := certificateD7_1164
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-21))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-19)) (.leaf (-23)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 10 (.leaf (0)) (.branch 17 (.leaf (-1)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 13 (.branch 2 (.leaf (-21)) (.leaf (-20))) (.branch 24 (.leaf (-19)) (.branch 28 (.leaf (-16)) (.leaf (-8))))),
  (.branch 20 (.branch 8 (.leaf (-23)) (.branch 14 (.leaf (-22)) (.leaf (-21)))) (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-15))) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 19 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-7)) (.leaf (-4))))),
  (.branch 25 (.branch 5 (.leaf (-17)) (.branch 15 (.leaf (-16)) (.leaf (-15)))) (.branch 27 (.branch 26 (.leaf (-12)) (.leaf (-9))) (.branch 28 (.leaf (-6)) (.leaf (-3))))),
  (.branch 18 (.leaf (-8)) (.leaf (-7))),
  (.branch 24 (.branch 22 (.branch 7 (.leaf (-17)) (.leaf (-16))) (.branch 23 (.leaf (-14)) (.leaf (-12)))) (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2))))))]
def witnessD7_062_1165 : CycleWitness 7 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (6)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (4)) (.leaf (2))) (.branch 24 (.leaf (5)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1165
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-23))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-19)) (.leaf (-22)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.branch 28 (.leaf (-1)) (.leaf (-4)))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-11)) (.leaf (-13))))]
  high := ![(.branch 17 (.branch 7 (.branch 2 (.leaf (-23)) (.leaf (-22))) (.branch 12 (.leaf (-21)) (.leaf (-20)))) (.branch 27 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 28 (.leaf (-12)) (.leaf (-6))))),
  (.branch 26 (.branch 14 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20)))) (.branch 27 (.leaf (-15)) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 21 (.leaf (-4)) (.branch 28 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (-4)),
  (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.branch 20 (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 27 (.leaf (-4)) (.branch 28 (.leaf (-3)) (.leaf (-2))))))]
def witnessD7_062_1166 : CycleWitness 7 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (6)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (2)) (.leaf (6)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1166
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-19)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-20)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-23)) (.leaf (-24)))),
  (.branch 10 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-25)) (.leaf (-23))) (.branch 24 (.leaf (-21)) (.branch 28 (.leaf (-19)) (.leaf (-12))))),
  (.branch 22 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-12)) (.leaf (-6))))),
  (.leaf (-2)),
  (.leaf (0)),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-18)) (.leaf (-16))) (.branch 23 (.leaf (-14)) (.leaf (-12)))) (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 23 (.branch 20 (.branch 18 (.leaf (-24)) (.branch 19 (.leaf (-22)) (.leaf (-20)))) (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-16)) (.leaf (-14))))) (.branch 26 (.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-8)))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 26 (.branch 11 (.leaf (-9)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2)))))]
def witnessD7_062_1167 : CycleWitness 7 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (6)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (6)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1167
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (-1)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-17)) (.leaf (-19)))),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 10 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 13 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-4)))),
  (.branch 27 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 22 (.leaf (-3)) (.leaf (0))),
  (.branch 25 (.branch 14 (.leaf (-19)) (.branch 24 (.leaf (-18)) (.leaf (-15)))) (.branch 27 (.branch 26 (.leaf (-12)) (.leaf (-9))) (.branch 28 (.leaf (-6)) (.leaf (-3))))),
  (.branch 23 (.branch 20 (.branch 4 (.leaf (-23)) (.branch 19 (.leaf (-22)) (.leaf (-20)))) (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-16)) (.leaf (-14))))) (.branch 26 (.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-8)))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 26 (.branch 11 (.leaf (-9)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2)))))]
def witnessD7_062_1168 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (5)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (6))))))
  code := certificateD7_1168
  counts := ![(.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 8 (.leaf (5)) (.leaf (6))) (.branch 10 (.leaf (7)) (.branch 12 (.leaf (8)) (.leaf (9)))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (10)) (.leaf (11))) (.branch 17 (.leaf (12)) (.branch 19 (.leaf (13)) (.leaf (14))))) (.branch 24 (.branch 22 (.leaf (15)) (.branch 23 (.leaf (16)) (.leaf (17)))) (.branch 26 (.leaf (18)) (.branch 27 (.leaf (19)) (.leaf (20))))))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 3 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 14 (.leaf (0)) (.leaf (-14))),
  (.branch 21 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 25 (.leaf (-6)) (.leaf (-5))),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 10 (.leaf (-19)) (.branch 11 (.leaf (-18)) (.leaf (-17))))) (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 17 (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))) (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.leaf (-8))))) (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_062_1169 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (5)) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (4)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (6)) (.branch 27 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1169
  counts := ![(.branch 13 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))))) (.branch 21 (.branch 16 (.branch 15 (.leaf (9)) (.leaf (10))) (.branch 18 (.leaf (11)) (.branch 19 (.leaf (12)) (.leaf (13))))) (.branch 24 (.branch 23 (.leaf (14)) (.leaf (15))) (.branch 26 (.leaf (16)) (.branch 27 (.leaf (17)) (.leaf (18))))))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 25 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 20 (.leaf (-11)) (.leaf (-9))),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-17)) (.leaf (-16))) (.branch 14 (.leaf (-15)) (.leaf (-14)))) (.branch 17 (.branch 16 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-11)) (.leaf (-10))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_062_1170 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (4)) (.leaf (0)))) (.branch 26 (.leaf (6)) (.branch 27 (.leaf (0)) (.leaf (1)))))))
  code := certificateD7_1170
  counts := ![(.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 18 (.leaf (10)) (.leaf (11)))) (.branch 23 (.branch 21 (.leaf (12)) (.leaf (13))) (.branch 25 (.leaf (14)) (.branch 27 (.leaf (15)) (.leaf (16))))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 7 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-18))),
  (.branch 24 (.leaf (0)) (.leaf (-4))),
  (.branch 12 (.leaf (0)) (.leaf (-16))),
  (.branch 26 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 24 (.branch 22 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 24 (.branch 23 (.leaf (-3)) (.leaf (-2))) (.branch 25 (.leaf (-1)) (.leaf (0)))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 14 (.branch 12 (.branch 11 (.leaf (-18)) (.leaf (-17))) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 16 (.branch 15 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.branch 16 (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_062_1171 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (6)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (1)))))))
  code := certificateD7_1171
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (7)) (.leaf (8))) (.branch 18 (.leaf (9)) (.leaf (10)))) (.branch 24 (.branch 22 (.leaf (11)) (.leaf (12))) (.branch 27 (.leaf (13)) (.leaf (14)))))),
  (.branch 14 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-16))),
  (.branch 26 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-19))),
  (.branch 23 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 16 (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 13 (.branch 11 (.branch 10 (.leaf (-19)) (.leaf (-18))) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 15 (.branch 14 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-13)) (.branch 17 (.leaf (-12)) (.leaf (-11)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_062_1172 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (4)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (3)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1172
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 15 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 23 (.branch 21 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 16 (.leaf (-7)) (.branch 18 (.leaf (-8)) (.leaf (-9))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 19 (.leaf (-16)) (.leaf (-17)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-15))),
  (.branch 27 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 24 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-6)))),
  (.branch 26 (.branch 20 (.leaf (-17)) (.leaf (-15))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.branch 6 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (0)))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.branch 16 (.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_062_1173 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (3)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (5)) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 25 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (0)))) (.branch 26 (.leaf (6)) (.branch 27 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1173
  counts := ![(.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 18 (.leaf (10)) (.leaf (11)))) (.branch 23 (.branch 22 (.leaf (12)) (.leaf (13))) (.branch 25 (.leaf (14)) (.branch 27 (.leaf (15)) (.leaf (16))))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 12 (.leaf (0)) (.leaf (-16))),
  (.branch 19 (.leaf (0)) (.leaf (-9))),
  (.branch 26 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 24 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 16 (.branch 10 (.branch 7 (.branch 6 (.leaf (-23)) (.leaf (-22))) (.branch 8 (.leaf (-21)) (.branch 9 (.leaf (-20)) (.leaf (-19))))) (.branch 13 (.branch 11 (.leaf (-18)) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))))) (.branch 22 (.branch 19 (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 20 (.branch 16 (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_062_1174 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (3)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (6)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1174
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (7)) (.leaf (8))) (.branch 18 (.leaf (9)) (.leaf (10)))) (.branch 25 (.branch 22 (.leaf (11)) (.leaf (12))) (.branch 27 (.leaf (13)) (.leaf (14)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-19))),
  (.branch 23 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 13 (.branch 11 (.branch 10 (.leaf (-19)) (.leaf (-18))) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 15 (.branch 14 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-13)) (.branch 17 (.leaf (-12)) (.leaf (-11)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_062_1175 : CycleWitness 7 where
  length := 28
  word := (.branch 15 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (4)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (0)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (4)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1175
  counts := ![(.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.leaf (15)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 13 (.leaf (-14)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 20 (.branch 16 (.branch 14 (.leaf (-16)) (.leaf (-15))) (.branch 18 (.leaf (-14)) (.leaf (-13)))) (.branch 24 (.branch 22 (.leaf (-12)) (.leaf (-11))) (.branch 26 (.leaf (-10)) (.leaf (-9))))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.leaf (-8)) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 21 (.branch 6 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.branch 17 (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))) (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.leaf (-8))))) (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_062_1176 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (5)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (6)) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1176
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (7)) (.leaf (8))) (.branch 18 (.leaf (9)) (.leaf (10)))) (.branch 25 (.branch 23 (.leaf (11)) (.leaf (12))) (.branch 27 (.leaf (13)) (.leaf (14)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-18))),
  (.branch 24 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 19 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 21 (.leaf (-2)) (.leaf (-1))),
  (.branch 27 (.leaf (-6)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 19 (.branch 14 (.branch 12 (.branch 11 (.leaf (-18)) (.leaf (-17))) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 16 (.branch 15 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 10 (.branch 7 (.branch 6 (.leaf (-23)) (.leaf (-22))) (.branch 8 (.leaf (-21)) (.branch 9 (.leaf (-20)) (.leaf (-19))))) (.branch 13 (.branch 11 (.leaf (-18)) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))))) (.branch 22 (.branch 19 (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_062_1177 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (1)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (3)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (6))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (1)))))))
  code := certificateD7_1177
  counts := ![(.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-17)) (.leaf (-34)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.leaf (-5)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (-1))) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-14)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 21 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 15 (.branch 6 (.branch 3 (.leaf (-34)) (.leaf (-33))) (.branch 9 (.leaf (-32)) (.branch 12 (.leaf (-31)) (.leaf (-30))))) (.branch 21 (.branch 18 (.leaf (-29)) (.leaf (-28))) (.branch 24 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-17)))))),
  (.branch 16 (.leaf (-5)) (.branch 26 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-3)),
  (.branch 22 (.branch 19 (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))) (.branch 20 (.leaf (-11)) (.branch 21 (.leaf (-10)) (.leaf (-9))))) (.branch 25 (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 26 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.leaf (-3)))),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 10 (.leaf (-19)) (.branch 11 (.leaf (-18)) (.leaf (-17))))) (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_062_1178 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 5 (.leaf (3)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (6)) (.leaf (0)))) (.branch 26 (.leaf (4)) (.branch 27 (.leaf (0)) (.leaf (1)))))))
  code := certificateD7_1178
  counts := ![(.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 18 (.leaf (10)) (.leaf (11)))) (.branch 23 (.branch 22 (.leaf (12)) (.leaf (13))) (.branch 25 (.leaf (14)) (.branch 27 (.leaf (15)) (.leaf (16))))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-18))),
  (.branch 24 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 24 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.branch 14 (.branch 12 (.branch 11 (.leaf (-18)) (.leaf (-17))) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 16 (.branch 15 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_062_1179 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 5 (.leaf (5)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 19 (.leaf (6)) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (1)))))))
  code := certificateD7_1179
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (7)) (.leaf (8))) (.branch 18 (.leaf (9)) (.leaf (10)))) (.branch 25 (.branch 23 (.leaf (11)) (.leaf (12))) (.branch 27 (.leaf (13)) (.leaf (14)))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-19)) (.leaf (-20)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (-4))) (.branch 26 (.leaf (-5)) (.leaf (-6)))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 19 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 21 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 24 (.branch 13 (.leaf (-20)) (.branch 23 (.leaf (-18)) (.leaf (-15)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 27 (.leaf (-6)) (.leaf (-3))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 10 (.branch 7 (.branch 6 (.leaf (-23)) (.leaf (-22))) (.branch 8 (.leaf (-21)) (.branch 9 (.leaf (-20)) (.leaf (-19))))) (.branch 13 (.branch 11 (.leaf (-18)) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))))) (.branch 22 (.branch 19 (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_062_1180 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (1)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1180
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 23 (.leaf (9)) (.branch 26 (.leaf (10)) (.leaf (11)))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.branch 19 (.leaf (-11)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4)))),
  (.branch 14 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 24 (.branch 3 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-13)) (.leaf (-8)))),
  (.branch 13 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-9))))),
  (.branch 26 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-11)) (.leaf (-7)))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 17 (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))) (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.leaf (-8))))) (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_062_1181 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (1)))))))
  code := certificateD7_1181
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 15 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 23 (.leaf (9)) (.branch 26 (.leaf (10)) (.leaf (11)))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 16 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-8)))),
  (.branch 27 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 24 (.branch 16 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-13)) (.leaf (-8)))),
  (.branch 17 (.leaf (-5)) (.branch 23 (.leaf (-4)) (.leaf (0)))),
  (.branch 25 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.branch 20 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_062_1182 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (3)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (4)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (6)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (2))) (.branch 27 (.leaf (1)) (.leaf (5)))))))
  code := certificateD7_1182
  counts := ![(.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 13 (.leaf (-6)) (.branch 24 (.leaf (-7)) (.leaf (-8))))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-10))))]
  high := ![(.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))),
  (.branch 16 (.leaf (-9)) (.branch 22 (.leaf (-7)) (.leaf (-5)))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.leaf (-7)))) (.branch 26 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.leaf (-3)))))]
def witnessD7_062_1183 : CycleWitness 7 where
  length := 28
  word := (.branch 15 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (6)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (0)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (4)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (6)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1183
  counts := ![(.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.leaf (15)))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 9 (.leaf (-18)) (.leaf (-24)))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (-5)) (.leaf (-8))))]
  high := ![(.branch 18 (.branch 12 (.branch 10 (.leaf (-24)) (.leaf (-23))) (.branch 14 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20))))) (.branch 22 (.branch 20 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.branch 26 (.leaf (-16)) (.leaf (-15)))))),
  (.branch 26 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.branch 19 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3)))))]
def witnessD7_062_1184 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (6)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (1)))))))
  code := certificateD7_1184
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (7)) (.leaf (8))) (.branch 18 (.leaf (9)) (.leaf (10)))) (.branch 24 (.branch 22 (.leaf (11)) (.leaf (12))) (.branch 26 (.leaf (13)) (.leaf (14)))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-25))),
  (.branch 17 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 15 (.branch 9 (.branch 6 (.branch 4 (.leaf (-25)) (.branch 5 (.leaf (-24)) (.leaf (-23)))) (.branch 7 (.leaf (-22)) (.branch 8 (.leaf (-21)) (.leaf (-20))))) (.branch 12 (.branch 10 (.leaf (-19)) (.branch 11 (.leaf (-18)) (.leaf (-17)))) (.branch 13 (.leaf (-16)) (.branch 14 (.leaf (-15)) (.leaf (-14)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (-13)) (.branch 17 (.leaf (-12)) (.leaf (-11)))) (.branch 19 (.leaf (-10)) (.branch 20 (.leaf (-9)) (.leaf (-8))))) (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_062_1185 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (6)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1185
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (11)) (.leaf (12)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 27 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-22))),
  (.branch 13 (.leaf (0)) (.leaf (-15))),
  (.branch 20 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 27 (.leaf (-6)) (.leaf (-3))),
  (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 19 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 17 (.branch 11 (.branch 8 (.branch 7 (.leaf (-22)) (.leaf (-21))) (.branch 9 (.leaf (-20)) (.branch 10 (.leaf (-19)) (.leaf (-18))))) (.branch 14 (.branch 12 (.leaf (-17)) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 20 (.branch 16 (.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_062_1186 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (6)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (4)))))))
  code := certificateD7_1186
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (11)) (.leaf (12)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-22)) (.leaf (-23)))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (-7))) (.branch 25 (.leaf (-8)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 27 (.leaf (-6)) (.leaf (-3))),
  (.branch 24 (.branch 22 (.branch 12 (.leaf (-23)) (.leaf (-21))) (.branch 23 (.leaf (-18)) (.leaf (-15)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 25 (.branch 5 (.leaf (-16)) (.branch 24 (.leaf (-15)) (.leaf (-12)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 19 (.leaf (-2)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_062_1187 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (4)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (3)) (.branch 19 (.leaf (1)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (6)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (4)))))))
  code := certificateD7_1187
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 11 (.leaf (-3)) (.branch 25 (.leaf (-5)) (.leaf (-7))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-16))) (.branch 22 (.leaf (-17)) (.leaf (-18)))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 21 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 21 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))),
  (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-15)) (.leaf (-12)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 9 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 10 (.leaf (-19)) (.branch 11 (.leaf (-18)) (.leaf (-17))))) (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_062_1188 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (5))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (6)))))))
  code := certificateD7_1188
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-5)) (.leaf (-6)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-16))) (.branch 22 (.leaf (-17)) (.leaf (-18)))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 21 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.leaf (-3)))),
  (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-15)) (.leaf (-12)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 9 (.leaf (-4)) (.leaf (-3))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_062_1189 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (4))) (.branch 20 (.leaf (0)) (.leaf (5))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (3)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1189
  counts := ![(.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 25 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.leaf (12)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 21 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-21)))]
  high := ![(.branch 18 (.leaf (-5)) (.branch 23 (.leaf (-4)) (.leaf (-3)))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 15 (.leaf (-14)) (.leaf (-12))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 10 (.leaf (-19)) (.branch 11 (.leaf (-18)) (.leaf (-17))))) (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_062_1190 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (3))) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (2)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (6)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (2)) (.leaf (1)))))))
  code := certificateD7_1190
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-21)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (-10))) (.branch 24 (.leaf (-11)) (.leaf (-12)))),
  (.branch 9 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 15 (.branch 4 (.leaf (-21)) (.leaf (-20))) (.branch 26 (.leaf (-19)) (.branch 27 (.leaf (-14)) (.leaf (-9))))),
  (.branch 24 (.branch 18 (.leaf (-3)) (.leaf (-2))) (.branch 25 (.leaf (-1)) (.leaf (0)))),
  (.branch 5 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-5)))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.branch 13 (.branch 11 (.branch 10 (.leaf (-19)) (.leaf (-18))) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 15 (.branch 14 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-13)) (.branch 17 (.leaf (-12)) (.leaf (-11)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_062_1191 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1191
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 24 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 13 (.leaf (0)) (.leaf (-15))),
  (.branch 25 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 21 (.branch 15 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))) (.branch 24 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.leaf (-3)))),
  (.branch 16 (.leaf (-9)) (.branch 22 (.leaf (-7)) (.leaf (-5)))),
  (.branch 9 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (0)))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 16 (.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_062_1192 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (5)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (6)))))))
  code := certificateD7_1192
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 20 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-16)) (.leaf (-17)))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 4 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-11)))),
  (.branch 26 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 25 (.branch 14 (.leaf (-17)) (.branch 24 (.leaf (-15)) (.leaf (-12)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_062_1193 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (6)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1193
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-19))),
  (.branch 23 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 20 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-3)))),
  (.branch 22 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 21 (.leaf (-1)) (.leaf (0))),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 13 (.branch 11 (.branch 10 (.leaf (-19)) (.leaf (-18))) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 15 (.branch 14 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-13)) (.branch 17 (.leaf (-12)) (.leaf (-11)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_062_1194 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (0))) (.branch 20 (.leaf (6)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (5)))))))
  code := certificateD7_1194
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (7)) (.leaf (8))) (.branch 19 (.leaf (9)) (.leaf (10)))) (.branch 25 (.branch 23 (.leaf (11)) (.leaf (12))) (.branch 27 (.leaf (13)) (.leaf (14)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-15))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-8)))]
  high := ![(.leaf (-1)),
  (.branch 24 (.branch 13 (.branch 3 (.leaf (-15)) (.leaf (-14))) (.branch 23 (.leaf (-13)) (.leaf (-11)))) (.branch 26 (.branch 25 (.leaf (-9)) (.leaf (-7))) (.branch 27 (.leaf (-5)) (.leaf (-3))))),
  (.branch 17 (.leaf (-6)) (.branch 27 (.leaf (-5)) (.leaf (-3)))),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_062_1195 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1195
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-16))) (.branch 22 (.leaf (-17)) (.leaf (-18)))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 25 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 21 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-15)) (.leaf (-12)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 9 (.leaf (-4)) (.leaf (-3))),
  (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-17)) (.leaf (-16))) (.branch 14 (.leaf (-15)) (.leaf (-14)))) (.branch 17 (.branch 16 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-11)) (.leaf (-10))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_062 : Fin 35 → CycleWitness 7 := ![witnessD7_062_1161, witnessD7_062_1162, witnessD7_062_1163, witnessD7_062_1164, witnessD7_062_1165, witnessD7_062_1166, witnessD7_062_1167, witnessD7_062_1168, witnessD7_062_1169, witnessD7_062_1170, witnessD7_062_1171, witnessD7_062_1172, witnessD7_062_1173, witnessD7_062_1174, witnessD7_062_1175, witnessD7_062_1176, witnessD7_062_1177, witnessD7_062_1178, witnessD7_062_1179, witnessD7_062_1180, witnessD7_062_1181, witnessD7_062_1182, witnessD7_062_1183, witnessD7_062_1184, witnessD7_062_1185, witnessD7_062_1186, witnessD7_062_1187, witnessD7_062_1188, witnessD7_062_1189, witnessD7_062_1190, witnessD7_062_1191, witnessD7_062_1192, witnessD7_062_1193, witnessD7_062_1194, witnessD7_062_1195]
end RealPinwheel.FiveSixths


