-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_064
-- name    : RealPinwheel_FiveSixths_WitnessD7_064
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:16:44.057226+00:00
-- url     : https://prove2.me/theorems/57f5454c-4e15-47fb-b87d-6ac63307bf39
-- title:
--   Exact witness block D7_064
-- statement:
--   These exact witnesses represent words 1232 through 1267 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 1232–1267; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_064_1231 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (5)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1231
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-18))) (.branch 18 (.leaf (-21)) (.leaf (-22)))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 23 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.branch 19 (.leaf (-22)) (.leaf (-20))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 5 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-5)))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_064_1232 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (2))) (.branch 13 (.leaf (1)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (6))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (4)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (3))) (.branch 27 (.leaf (5)) (.leaf (2)))))))
  code := certificateD7_1232
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-11)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-18)) (.leaf (-19)))),
  (.branch 16 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 9 (.leaf (0)) (.branch 17 (.leaf (-1)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 25 (.branch 6 (.leaf (-13)) (.leaf (-12))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 20 (.branch 14 (.leaf (-19)) (.leaf (-17))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 17 (.leaf (-5)) (.branch 23 (.leaf (-4)) (.leaf (0)))),
  (.branch 19 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 27 (.leaf (-10)) (.leaf (-7)))),
  (.branch 25 (.branch 5 (.leaf (-16)) (.branch 24 (.leaf (-15)) (.leaf (-12)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 18 (.leaf (-4)) (.leaf (-3))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_064_1233 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (6)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1233
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-18))),
  (.branch 24 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 26 (.leaf (-6)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 24 (.leaf (-3)) (.leaf (-2))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 14 (.branch 12 (.branch 11 (.leaf (-18)) (.leaf (-17))) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 16 (.branch 15 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_064_1234 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (2)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (6)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (3)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (2)) (.leaf (4))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (6)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1234
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-19))) (.branch 21 (.leaf (-20)) (.leaf (-21)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 26 (.leaf (-6)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.leaf (-1)) (.leaf (0))),
  (.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.branch 24 (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-18)) (.leaf (-15)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 8 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_064_1235 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (6)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (3)) (.leaf (1)))))))
  code := certificateD7_1235
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 14 (.leaf (-14)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-7)) (.leaf (-8)))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 26 (.leaf (-9)) (.leaf (-10)))),
  (.branch 9 (.leaf (0)) (.branch 17 (.leaf (-1)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 6 (.leaf (0)) (.leaf (-22))),
  (.branch 20 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 26 (.branch 15 (.leaf (-20)) (.leaf (-19))) (.branch 27 (.leaf (-14)) (.leaf (-9)))),
  (.branch 25 (.branch 20 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-3)) (.leaf (0)))),
  (.branch 27 (.leaf (-10)) (.leaf (-5))),
  (.branch 18 (.leaf (-4)) (.leaf (-3))),
  (.branch 24 (.branch 4 (.leaf (-13)) (.branch 14 (.leaf (-12)) (.leaf (-11)))) (.branch 26 (.branch 25 (.leaf (-9)) (.leaf (-7))) (.branch 27 (.leaf (-5)) (.leaf (-3))))),
  (.branch 17 (.branch 11 (.branch 8 (.branch 7 (.leaf (-22)) (.leaf (-21))) (.branch 9 (.leaf (-20)) (.branch 10 (.leaf (-19)) (.leaf (-18))))) (.branch 14 (.branch 12 (.leaf (-17)) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_064_1236 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (1)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (4)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1236
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-18))) (.branch 24 (.leaf (-19)) (.leaf (-20)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-3)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 21 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.branch 25 (.leaf (-20)) (.leaf (-15))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.branch 11 (.leaf (-6)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_064_1237 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (6)) (.leaf (1))) (.branch 13 (.leaf (3)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (6)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (4)))))))
  code := certificateD7_1237
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-11)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 14 (.leaf (-3)) (.branch 25 (.leaf (-4)) (.leaf (-5))))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 11 (.leaf (0)) (.branch 23 (.leaf (-4)) (.leaf (-7))))]
  high := ![(.branch 25 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 3 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-6)))),
  (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-1)),
  (.branch 9 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (0)))),
  (.branch 22 (.branch 19 (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 24 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3)))))]
def witnessD7_064_1238 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (2))) (.branch 13 (.leaf (5)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (6)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (5)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (2))) (.branch 27 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1238
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 4 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-15)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 18 (.leaf (-5)) (.leaf (-3)))]
def witnessD7_064_1239 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (5)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (6)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (4)) (.branch 23 (.leaf (5)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1239
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 12 (.leaf (-15)) (.leaf (-21)))),
  (.branch 27 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-2)) (.leaf (-3)))),
  (.branch 22 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-16)) (.leaf (-17)))),
  (.branch 3 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 21 (.branch 11 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 25 (.branch 13 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-11)) (.leaf (-7))))),
  (.leaf (-1)),
  (.branch 12 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 25 (.branch 14 (.leaf (-17)) (.branch 24 (.leaf (-15)) (.leaf (-12)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_064_1240 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (6))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (2)) (.leaf (5)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1240
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 27 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-1)) (.leaf (-2)))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 26 (.branch 21 (.leaf (-18)) (.leaf (-16))) (.branch 27 (.leaf (-13)) (.leaf (-10)))),
  (.leaf (-5)),
  (.branch 25 (.branch 16 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.leaf (-2)) (.leaf (0))),
  (.branch 25 (.branch 5 (.leaf (-11)) (.branch 15 (.leaf (-10)) (.leaf (-9)))) (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-5)) (.leaf (-3))))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_064_1241 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (5))) (.branch 13 (.leaf (2)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (3)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (6)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (3)) (.leaf (1)))))))
  code := certificateD7_1241
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-7)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-18))) (.branch 24 (.leaf (-19)) (.leaf (-20)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 21 (.leaf (-6)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-8)))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 25 (.branch 24 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3))))),
  (.branch 23 (.leaf (-2)) (.leaf (0))),
  (.branch 26 (.branch 25 (.leaf (-20)) (.leaf (-15))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.branch 22 (.leaf (-7)) (.leaf (-5))),
  (.branch 26 (.branch 16 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-5)) (.leaf (-3)))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 23 (.branch 21 (.branch 5 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.leaf (-8)))) (.branch 25 (.branch 24 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3))))))]
def witnessD7_064_1242 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (6))) (.branch 13 (.leaf (0)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (2)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (1))) (.branch 20 (.leaf (5)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (1)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (6))) (.branch 27 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1242
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.leaf (-2)) (.leaf (0))),
  (.branch 25 (.branch 5 (.leaf (-11)) (.branch 15 (.leaf (-10)) (.leaf (-9)))) (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-5)) (.leaf (-3))))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_064_1243 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (4)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (4))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (6)) (.branch 23 (.leaf (1)) (.leaf (3)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (4)) (.leaf (1)))))))
  code := certificateD7_1243
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-20))),
  (.branch 22 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 21 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 19 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 22 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-20)) (.leaf (-19))) (.branch 11 (.leaf (-18)) (.branch 12 (.leaf (-17)) (.leaf (-16))))) (.branch 15 (.branch 14 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-13)) (.branch 17 (.leaf (-12)) (.leaf (-11)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_064_1244 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (3))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (2)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (2)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (5)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (6)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (3))) (.branch 27 (.leaf (1)) (.leaf (5)))))))
  code := certificateD7_1244
  counts := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-23))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 25 (.branch 2 (.leaf (-23)) (.branch 19 (.leaf (-22)) (.leaf (-20)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 16 (.leaf (-9)) (.branch 22 (.leaf (-7)) (.leaf (-5)))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.leaf (-1)) (.leaf (0))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_064_1245 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (2)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (2)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (2)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1245
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-22))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (-13))) (.branch 23 (.leaf (-14)) (.leaf (-15)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 26 (.leaf (-6)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 24 (.branch 22 (.branch 3 (.leaf (-22)) (.leaf (-21))) (.branch 23 (.leaf (-18)) (.leaf (-15)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 25 (.branch 24 (.leaf (-15)) (.leaf (-12))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 17 (.leaf (-8)) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 10 (.leaf (-1)) (.leaf (0)))]
def witnessD7_064_1246 : CycleWitness 7 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (5)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1246
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-11)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-15))),
  (.branch 27 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 25 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 27 (.leaf (-6)) (.leaf (-3))),
  (.branch 19 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.branch 16 (.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_064_1247 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (6)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (6)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (3))) (.branch 19 (.leaf (1)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (4)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1247
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-10)) (.leaf (-14))))]
  high := ![(.branch 18 (.branch 4 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))),
  (.branch 20 (.branch 3 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-3)))),
  (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 23 (.branch 8 (.leaf (-13)) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-14)) (.leaf (-13))) (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10))))) (.branch 24 (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7)))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4))))))]
def witnessD7_064_1248 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1248
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 23 (.branch 21 (.leaf (9)) (.leaf (10))) (.branch 25 (.leaf (11)) (.leaf (12)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.branch 7 (.leaf (-7)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-19)) (.leaf (-20)))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-14))),
  (.branch 26 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 26 (.leaf (-8)) (.leaf (-4))),
  (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-20)) (.leaf (-18))) (.branch 20 (.leaf (-16)) (.branch 21 (.leaf (-14)) (.leaf (-12))))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 24 (.branch 9 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-8)))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 20 (.branch 16 (.branch 14 (.leaf (-14)) (.branch 15 (.leaf (-13)) (.leaf (-12)))) (.branch 18 (.branch 17 (.leaf (-11)) (.leaf (-10))) (.branch 19 (.leaf (-9)) (.leaf (-8))))) (.branch 23 (.branch 21 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_064_1249 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (4)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (6)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1249
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 23 (.branch 21 (.leaf (9)) (.leaf (10))) (.branch 25 (.leaf (11)) (.leaf (12)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.branch 7 (.leaf (-7)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-19)) (.leaf (-22)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-19)) (.leaf (-20)))),
  (.branch 11 (.leaf (0)) (.leaf (-16))),
  (.branch 24 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 26 (.leaf (-8)) (.leaf (-4))),
  (.branch 23 (.branch 9 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 25 (.branch 24 (.leaf (-16)) (.leaf (-12))) (.branch 26 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-4)),
  (.leaf (0)),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-20)) (.leaf (-18))) (.branch 20 (.leaf (-16)) (.branch 21 (.leaf (-14)) (.leaf (-12))))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-16)) (.leaf (-15))) (.branch 14 (.leaf (-14)) (.leaf (-13)))) (.branch 17 (.branch 16 (.leaf (-12)) (.leaf (-11))) (.branch 18 (.leaf (-10)) (.leaf (-9))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-8)) (.leaf (-7))) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_064_1250 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (6)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1250
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 25 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-10)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 24 (.leaf (-11)) (.leaf (-18)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-15)))),
  (.branch 10 (.leaf (0)) (.leaf (-17))),
  (.branch 23 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 20 (.branch 17 (.leaf (-13)) (.leaf (-12))) (.branch 23 (.leaf (-11)) (.branch 26 (.leaf (-10)) (.leaf (-6))))),
  (.branch 25 (.leaf (-18)) (.branch 26 (.leaf (-14)) (.leaf (-10)))),
  (.leaf (-4)),
  (.leaf (0)),
  (.branch 21 (.branch 18 (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))) (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10))))) (.branch 24 (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7)))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 18 (.branch 14 (.branch 12 (.branch 11 (.leaf (-17)) (.leaf (-16))) (.branch 13 (.leaf (-15)) (.leaf (-14)))) (.branch 16 (.branch 15 (.leaf (-13)) (.leaf (-12))) (.branch 17 (.leaf (-11)) (.leaf (-10))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 21 (.leaf (-7)) (.leaf (-6)))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_064_1251 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (6)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (5)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1251
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 25 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-10)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 24 (.leaf (-11)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2)))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-15))))]
  high := ![(.branch 20 (.branch 17 (.leaf (-13)) (.leaf (-12))) (.branch 23 (.leaf (-11)) (.branch 26 (.leaf (-10)) (.leaf (-6))))),
  (.branch 25 (.leaf (-18)) (.branch 26 (.leaf (-14)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 23 (.branch 21 (.branch 7 (.leaf (-15)) (.leaf (-14))) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 21 (.branch 18 (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))) (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10))))) (.branch 24 (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7)))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4))))))]
def witnessD7_064_1252 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1252
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-18))),
  (.branch 18 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 13 (.branch 11 (.branch 10 (.leaf (-18)) (.leaf (-17))) (.branch 12 (.leaf (-16)) (.leaf (-15)))) (.branch 15 (.branch 14 (.leaf (-14)) (.leaf (-13))) (.branch 16 (.leaf (-12)) (.branch 17 (.leaf (-11)) (.leaf (-10)))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 21 (.leaf (-7)) (.leaf (-6)))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 21 (.leaf (-7)) (.leaf (-6)))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_064_1253 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (0)) (.leaf (5)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1253
  counts := ![(.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (11)) (.leaf (12)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 20 (.leaf (-5)) (.leaf (-4))),
  (.branch 23 (.branch 21 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-16))) (.branch 21 (.leaf (-14)) (.leaf (-12)))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 24 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD7_064_1254 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (4)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (5)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (2))) (.branch 26 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1254
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-19))),
  (.branch 17 (.leaf (0)) (.leaf (-10))),
  (.branch 26 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.leaf (-4)) (.leaf (-2))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-19)) (.leaf (-18))) (.branch 11 (.leaf (-17)) (.leaf (-16)))) (.branch 14 (.branch 13 (.leaf (-15)) (.leaf (-14))) (.branch 15 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-11)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-10)) (.leaf (-9))) (.branch 20 (.leaf (-8)) (.branch 21 (.leaf (-7)) (.leaf (-6))))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-10)) (.leaf (-9))) (.branch 20 (.leaf (-8)) (.branch 21 (.leaf (-7)) (.leaf (-6))))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_064_1255 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (3)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (5)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1255
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-20)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 25 (.branch 21 (.leaf (-22)) (.leaf (-21))) (.branch 26 (.leaf (-14)) (.leaf (-7)))),
  (.leaf (-2)),
  (.branch 12 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-8)))),
  (.branch 24 (.branch 13 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-16)) (.leaf (-14))) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 20 (.branch 17 (.branch 15 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-11)))) (.branch 18 (.leaf (-10)) (.branch 19 (.leaf (-9)) (.leaf (-8))))) (.branch 23 (.branch 21 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_064_1256 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (5)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (6))) (.branch 26 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1256
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-10)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.branch 25 (.leaf (-1)) (.leaf (-3))))]
  high := ![(.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.branch 20 (.leaf (-9)) (.leaf (-8))))) (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 24 (.branch 8 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2))))),
  (.branch 26 (.leaf (-3)) (.leaf (-2)))]
def witnessD7_064_1257 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (5)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (6)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (3)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (5)) (.leaf (3)))))))
  code := certificateD7_1257
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-20))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-15)) (.leaf (-17)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-7)) (.leaf (-9))))]
  high := ![(.branch 14 (.branch 6 (.branch 2 (.leaf (-20)) (.leaf (-19))) (.branch 10 (.leaf (-18)) (.leaf (-17)))) (.branch 22 (.branch 18 (.leaf (-16)) (.leaf (-15))) (.branch 26 (.leaf (-14)) (.leaf (-7))))),
  (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 24 (.branch 17 (.leaf (-17)) (.leaf (-16))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 22 (.branch 19 (.branch 5 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-16)) (.branch 21 (.leaf (-14)) (.leaf (-12))))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 13 (.leaf (-3)) (.leaf (-2))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.leaf (-2)))))]
def witnessD7_064_1258 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (5))) (.branch 19 (.leaf (1)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (6)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (5)))))))
  code := certificateD7_1258
  counts := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-22)) (.leaf (-24)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 16 (.leaf (-8)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 24 (.branch 7 (.leaf (-24)) (.branch 18 (.leaf (-23)) (.leaf (-20)))) (.branch 25 (.leaf (-15)) (.branch 26 (.leaf (-10)) (.leaf (-5))))),
  (.branch 20 (.branch 3 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-3)))),
  (.branch 4 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (-3)))),
  (.branch 25 (.branch 17 (.leaf (-13)) (.leaf (-12))) (.branch 26 (.leaf (-10)) (.leaf (-8)))),
  (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 23 (.branch 8 (.leaf (-13)) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))))]
def witnessD7_064_1259 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (5)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1259
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-17)) (.leaf (-19)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-1)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-15)) (.leaf (-17)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 21 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2)))),
  (.branch 19 (.branch 8 (.leaf (-19)) (.leaf (-18))) (.branch 25 (.leaf (-15)) (.branch 26 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-3)),
  (.branch 24 (.branch 17 (.leaf (-17)) (.leaf (-16))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-8)) (.leaf (-4))))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-16)) (.leaf (-14))) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.branch 9 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-8)))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD7_064_1260 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (6)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (5)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1260
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 17 (.leaf (-20)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-13)) (.leaf (-17)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 12 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 25 (.branch 18 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-17)) (.leaf (-10)))),
  (.branch 11 (.branch 3 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 19 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.leaf (-7))))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 23 (.branch 21 (.leaf (-17)) (.branch 22 (.leaf (-15)) (.leaf (-13)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-9))) (.branch 26 (.leaf (-7)) (.leaf (-5))))),
  (.branch 24 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 22 (.branch 20 (.branch 6 (.leaf (-17)) (.leaf (-16))) (.branch 21 (.leaf (-14)) (.leaf (-12)))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 13 (.leaf (-2)) (.branch 14 (.leaf (-1)) (.leaf (0))))]
def witnessD7_064_1261 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (1)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (5)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (2)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1261
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-20)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.leaf (0))]
  high := ![(.branch 25 (.branch 21 (.leaf (-22)) (.leaf (-21))) (.branch 26 (.leaf (-14)) (.leaf (-7)))),
  (.leaf (-2)),
  (.branch 24 (.branch 13 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 12 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-16)) (.leaf (-14))) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD7_064_1262 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (6))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1262
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 3 (.leaf (-5)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-5)))),
  (.branch 25 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2)))),
  (.branch 23 (.branch 14 (.leaf (-3)) (.leaf (-2))) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 16 (.branch 11 (.branch 8 (.branch 7 (.leaf (-21)) (.leaf (-20))) (.branch 9 (.leaf (-19)) (.branch 10 (.leaf (-18)) (.leaf (-17))))) (.branch 13 (.branch 12 (.leaf (-16)) (.leaf (-15))) (.branch 14 (.leaf (-14)) (.branch 15 (.leaf (-13)) (.leaf (-12)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-11)) (.leaf (-10))) (.branch 19 (.leaf (-9)) (.branch 20 (.leaf (-8)) (.leaf (-7))))) (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 21 (.leaf (-7)) (.leaf (-6)))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_064_1263 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (5)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (6))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (5)))))))
  code := certificateD7_1263
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-8)) (.leaf (-10))))]
  high := ![(.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 3 (.leaf (-5)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-5)))),
  (.branch 25 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2)))),
  (.branch 24 (.branch 9 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-8)))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.leaf (-7)))) (.branch 24 (.branch 23 (.leaf (-6)) (.leaf (-5))) (.branch 25 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2))))))]
def witnessD7_064_1264 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (6))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (3))) (.branch 26 (.leaf (2)) (.leaf (1)))))))
  code := certificateD7_1264
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-8)) (.leaf (-10))))]
  high := ![(.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.branch 22 (.leaf (-4)) (.leaf (-3))) (.branch 24 (.leaf (-2)) (.branch 25 (.leaf (-1)) (.leaf (0))))),
  (.branch 10 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-5)))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 24 (.branch 4 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.leaf (-7)))) (.branch 24 (.branch 23 (.leaf (-6)) (.leaf (-5))) (.branch 25 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2))))))]
def witnessD7_064_1265 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (1))) (.branch 19 (.leaf (5)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (6)) (.leaf (1)))))))
  code := certificateD7_1265
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-20)) (.leaf (-25)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-11)) (.leaf (-15)))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 17 (.branch 9 (.leaf (-25)) (.branch 13 (.leaf (-24)) (.leaf (-23)))) (.branch 25 (.branch 21 (.leaf (-22)) (.leaf (-21))) (.branch 26 (.leaf (-14)) (.leaf (-7))))),
  (.branch 23 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.leaf (-2)))),
  (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-13)) (.leaf (-11)))) (.branch 25 (.leaf (-9)) (.branch 26 (.leaf (-7)) (.leaf (-5))))),
  (.branch 12 (.leaf (-5)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-16)) (.leaf (-14))) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2))]
def witnessD7_064_1266 : CycleWitness 7 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (5)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (6)) (.leaf (1))) (.branch 26 (.leaf (3)) (.leaf (4)))))))
  code := certificateD7_1266
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-19)) (.leaf (-22)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-19)) (.leaf (-20)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.leaf (-4)) (.leaf (-2))),
  (.branch 23 (.branch 9 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 25 (.branch 24 (.leaf (-16)) (.leaf (-12))) (.branch 26 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-4)),
  (.leaf (0)),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-20)) (.leaf (-18))) (.branch 20 (.leaf (-16)) (.branch 21 (.leaf (-14)) (.leaf (-12))))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2))))]
def witnessD7_064 : Fin 36 → CycleWitness 7 := ![witnessD7_064_1231, witnessD7_064_1232, witnessD7_064_1233, witnessD7_064_1234, witnessD7_064_1235, witnessD7_064_1236, witnessD7_064_1237, witnessD7_064_1238, witnessD7_064_1239, witnessD7_064_1240, witnessD7_064_1241, witnessD7_064_1242, witnessD7_064_1243, witnessD7_064_1244, witnessD7_064_1245, witnessD7_064_1246, witnessD7_064_1247, witnessD7_064_1248, witnessD7_064_1249, witnessD7_064_1250, witnessD7_064_1251, witnessD7_064_1252, witnessD7_064_1253, witnessD7_064_1254, witnessD7_064_1255, witnessD7_064_1256, witnessD7_064_1257, witnessD7_064_1258, witnessD7_064_1259, witnessD7_064_1260, witnessD7_064_1261, witnessD7_064_1262, witnessD7_064_1263, witnessD7_064_1264, witnessD7_064_1265, witnessD7_064_1266]
end RealPinwheel.FiveSixths


