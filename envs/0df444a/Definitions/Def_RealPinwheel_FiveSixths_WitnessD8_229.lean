-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_229
-- name    : RealPinwheel_FiveSixths_WitnessD8_229
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T07:11:40.004914+00:00
-- url     : https://prove2.me/theorems/12484f37-4c7c-4c65-8e40-79a061e6a554
-- title:
--   Exact witness block D8_229
-- statement:
--   These exact witnesses represent words 2977 through 3005 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 2977–3005; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_229_2976 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (6)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (5)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (4))) (.branch 24 (.leaf (1)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (7)) (.leaf (1))) (.branch 28 (.leaf (0)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (6)) (.leaf (4))))))))
  code := certificateD8_2976
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 27 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-16)) (.leaf (-17)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 32 (.leaf (-15)) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 28 (.leaf (-10)) (.branch 33 (.leaf (-8)) (.leaf (-5)))),
  (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 31 (.branch 18 (.leaf (-17)) (.branch 30 (.leaf (-15)) (.leaf (-12)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_229_2977 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (5)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (2)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (7)) (.branch 33 (.leaf (2)) (.leaf (3))))))))
  code := certificateD8_2977
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 25 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 15 (.leaf (0)) (.leaf (-19))),
  (.branch 32 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 32 (.branch 27 (.leaf (-15)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 32 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (-2)),
  (.leaf (0)),
  (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 19 (.branch 17 (.branch 16 (.leaf (-19)) (.leaf (-18))) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 21 (.branch 20 (.leaf (-15)) (.leaf (-14))) (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_229_2978 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (6)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (4))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (6)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (3))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (4)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (7)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (5))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (3)) (.leaf (2))))))))
  code := certificateD8_2978
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 19 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-15)) (.leaf (-18)))),
  (.branch 9 (.leaf (0)) (.branch 31 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 31 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 32 (.leaf (-4)) (.branch 33 (.leaf (-3)) (.leaf (-2))))),
  (.branch 33 (.leaf (-3)) (.leaf (-2))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.leaf (-2)),
  (.branch 29 (.branch 27 (.branch 15 (.leaf (-18)) (.leaf (-17))) (.branch 28 (.leaf (-15)) (.leaf (-13)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-9))) (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-5)) (.leaf (-3)))),
  (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_229_2979 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (7)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (6)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (7)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (6))) (.branch 24 (.leaf (4)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (5)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (6)) (.leaf (2))))))))
  code := certificateD8_2979
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-12))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-14)))),
  (.branch 11 (.leaf (0)) (.branch 33 (.leaf (-1)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 26 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 30 (.branch 28 (.leaf (-14)) (.branch 29 (.leaf (-12)) (.leaf (-10)))) (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 31 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 30 (.branch 17 (.leaf (-14)) (.branch 29 (.leaf (-13)) (.leaf (-11)))) (.branch 32 (.branch 31 (.leaf (-9)) (.leaf (-7))) (.branch 33 (.leaf (-5)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_229_2980 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (7)) (.branch 16 (.leaf (3)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (6))) (.branch 24 (.leaf (1)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (5)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (7)) (.branch 33 (.leaf (4)) (.leaf (1))))))))
  code := certificateD8_2980
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 13 (.leaf (-15)) (.leaf (-16))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 20 (.leaf (-4)) (.branch 24 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.leaf (-22))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (-4)) (.leaf (-5)))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 32 (.branch 31 (.leaf (-16)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 30 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-1)) (.leaf (0))))),
  (.branch 26 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 30 (.branch 28 (.branch 5 (.leaf (-22)) (.leaf (-21))) (.branch 29 (.leaf (-18)) (.leaf (-15)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.leaf (-5)) (.leaf (-3))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_229_2981 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (7)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (6)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (5)) (.leaf (1))))))))
  code := certificateD8_2981
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 13 (.leaf (-15)) (.leaf (-16))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 20 (.leaf (-4)) (.branch 24 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-22))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (-4)) (.leaf (-5)))),
  (.branch 28 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.leaf (-23)))]
  high := ![(.branch 32 (.branch 31 (.leaf (-16)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 30 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-1)) (.leaf (0))))),
  (.branch 26 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 24 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 30 (.branch 28 (.branch 5 (.leaf (-22)) (.leaf (-21))) (.branch 29 (.leaf (-18)) (.leaf (-15)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.leaf (-5)) (.leaf (-3))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-23)) (.leaf (-22))) (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19))))) (.branch 19 (.branch 17 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_229_2982 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (5))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (7)) (.leaf (1))) (.branch 24 (.leaf (3)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (5))) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_2982
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-27)) (.leaf (-30)))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-29))),
  (.branch 22 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 31 (.branch 21 (.leaf (-30)) (.branch 26 (.leaf (-29)) (.leaf (-28)))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-14)) (.leaf (-7))))),
  (.branch 14 (.branch 4 (.leaf (-13)) (.branch 9 (.leaf (-12)) (.leaf (-11)))) (.branch 24 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.leaf (-7))))),
  (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 33 (.leaf (-4)) (.leaf (-2))),
  (.branch 31 (.branch 30 (.leaf (-10)) (.leaf (-8))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 19 (.branch 12 (.branch 8 (.branch 6 (.leaf (-29)) (.branch 7 (.leaf (-28)) (.leaf (-27)))) (.branch 10 (.branch 9 (.leaf (-26)) (.leaf (-25))) (.branch 11 (.leaf (-24)) (.leaf (-23))))) (.branch 15 (.branch 13 (.leaf (-22)) (.branch 14 (.leaf (-21)) (.leaf (-20)))) (.branch 17 (.branch 16 (.leaf (-19)) (.leaf (-18))) (.branch 18 (.leaf (-17)) (.leaf (-16)))))) (.branch 26 (.branch 22 (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-11))) (.branch 25 (.leaf (-10)) (.leaf (-9))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_229_2983 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (4)) (.leaf (6))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (1)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (7))))))))
  code := certificateD8_2983
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 13 (.leaf (-4)) (.branch 30 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-24)) (.leaf (-27)))),
  (.branch 5 (.leaf (0)) (.branch 32 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-7)) (.leaf (-8)))),
  (.branch 17 (.leaf (0)) (.leaf (-17))),
  (.leaf (0))]
  high := ![(.branch 32 (.branch 19 (.leaf (-13)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 32 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 30 (.branch 16 (.leaf (-27)) (.branch 23 (.leaf (-26)) (.leaf (-25)))) (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5))))),
  (.branch 33 (.leaf (-10)) (.leaf (-5))),
  (.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.branch 31 (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3))))),
  (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (-17)) (.leaf (-16))) (.branch 20 (.leaf (-15)) (.leaf (-14)))) (.branch 23 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.leaf (-10))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_229_2984 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (5))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (7))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (3)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (5)) (.leaf (2))) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (6))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (3)) (.leaf (7))))))))
  code := certificateD8_2984
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-27)) (.leaf (-31)))),
  (.branch 3 (.leaf (0)) (.branch 32 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 29 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-15)) (.leaf (-18)))),
  (.branch 9 (.leaf (0)) (.branch 31 (.leaf (-5)) (.leaf (-7)))),
  (.leaf (0))]
  high := ![(.branch 26 (.branch 16 (.leaf (-31)) (.branch 21 (.leaf (-30)) (.leaf (-29)))) (.branch 32 (.branch 31 (.leaf (-28)) (.leaf (-21))) (.branch 33 (.leaf (-14)) (.leaf (-7))))),
  (.branch 33 (.leaf (-14)) (.leaf (-7))),
  (.branch 30 (.branch 28 (.leaf (-14)) (.branch 29 (.leaf (-12)) (.leaf (-10)))) (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.branch 31 (.branch 30 (.leaf (-7)) (.leaf (-6))) (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3))))),
  (.branch 29 (.branch 27 (.branch 15 (.leaf (-18)) (.leaf (-17))) (.branch 28 (.leaf (-15)) (.leaf (-13)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-9))) (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-5)) (.leaf (-3)))),
  (.leaf (0))]
def witnessD8_229_2985 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (1))) (.branch 24 (.leaf (3)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (4))) (.branch 28 (.leaf (1)) (.leaf (7)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_2985
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-27)) (.leaf (-30)))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-4)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 31 (.branch 21 (.leaf (-30)) (.branch 26 (.leaf (-29)) (.leaf (-28)))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-14)) (.leaf (-7))))),
  (.branch 14 (.branch 4 (.leaf (-13)) (.branch 9 (.leaf (-12)) (.leaf (-11)))) (.branch 24 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.leaf (-7))))),
  (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 33 (.leaf (-4)) (.leaf (-2))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_229_2986 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (6)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (4)) (.leaf (5))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (1)) (.leaf (7)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (6)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))))))
  code := certificateD8_2986
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 13 (.leaf (-4)) (.branch 30 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-24)) (.leaf (-27)))),
  (.branch 5 (.leaf (0)) (.branch 32 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 32 (.branch 19 (.leaf (-13)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 32 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 30 (.branch 16 (.leaf (-27)) (.branch 23 (.leaf (-26)) (.leaf (-25)))) (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5))))),
  (.branch 33 (.leaf (-10)) (.leaf (-5))),
  (.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_229_2987 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (7))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (7))) (.branch 24 (.leaf (0)) (.leaf (3))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (4))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (6)) (.leaf (1))))))))
  code := certificateD8_2987
  counts := ![(.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-25))) (.branch 25 (.leaf (-26)) (.leaf (-27)))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-7)) (.leaf (-8)))),
  (.branch 22 (.leaf (0)) (.branch 33 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 33 (.leaf (-12)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 30 (.branch 20 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-10)))) (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-27)) (.leaf (-24))) (.branch 28 (.leaf (-21)) (.leaf (-18)))) (.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 32 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 31 (.branch 17 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_229_2988 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (5)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (4)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (3)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (7)) (.branch 33 (.leaf (5)) (.leaf (1))))))))
  code := certificateD8_2988
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 13 (.leaf (-15)) (.leaf (-16))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 16 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-19))),
  (.branch 32 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 32 (.branch 31 (.leaf (-16)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 30 (.leaf (-3)) (.leaf (0))),
  (.branch 32 (.leaf (-12)) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 24 (.branch 19 (.branch 17 (.branch 16 (.leaf (-19)) (.leaf (-18))) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 21 (.branch 20 (.leaf (-15)) (.leaf (-14))) (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_229_2989 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (2))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (5)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (4)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (5))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (4))) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (5)) (.leaf (4))))))))
  code := certificateD8_2989
  counts := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-14)) (.leaf (-16)))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 32 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 30 (.leaf (-19)) (.leaf (-20)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 22 (.leaf (0)) (.leaf (-12))),
  (.branch 5 (.leaf (0)) (.leaf (-29)))]
  high := ![(.branch 31 (.branch 24 (.leaf (-16)) (.branch 30 (.leaf (-15)) (.leaf (-12)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 33 (.leaf (-4)) (.leaf (-3))),
  (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 21 (.branch 14 (.leaf (-3)) (.leaf (-2))) (.branch 28 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-2)),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 12 (.branch 8 (.branch 6 (.leaf (-29)) (.branch 7 (.leaf (-28)) (.leaf (-27)))) (.branch 10 (.branch 9 (.leaf (-26)) (.leaf (-25))) (.branch 11 (.leaf (-24)) (.leaf (-23))))) (.branch 15 (.branch 13 (.leaf (-22)) (.branch 14 (.leaf (-21)) (.leaf (-20)))) (.branch 17 (.branch 16 (.leaf (-19)) (.leaf (-18))) (.branch 18 (.leaf (-17)) (.leaf (-16)))))) (.branch 26 (.branch 22 (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-11))) (.branch 25 (.leaf (-10)) (.leaf (-9))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_229_2990 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (6)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (4)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (2)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (4)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (7)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (4)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (3)) (.leaf (1))))))))
  code := certificateD8_2990
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-27))),
  (.branch 24 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 32 (.branch 27 (.leaf (-15)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 30 (.leaf (-3)) (.leaf (0))),
  (.branch 32 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 33 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.branch 13 (.branch 10 (.branch 8 (.leaf (-27)) (.branch 9 (.leaf (-26)) (.leaf (-25)))) (.branch 11 (.leaf (-24)) (.branch 12 (.leaf (-23)) (.leaf (-22))))) (.branch 16 (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19)))) (.branch 18 (.branch 17 (.leaf (-18)) (.leaf (-17))) (.branch 19 (.leaf (-16)) (.leaf (-15)))))) (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_229_2991 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (7)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (5)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (2)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (4)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (7)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (5)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (6)) (.branch 33 (.leaf (3)) (.leaf (1))))))))
  code := certificateD8_2991
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 32 (.branch 27 (.leaf (-15)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 30 (.leaf (-3)) (.leaf (0))),
  (.branch 32 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.leaf (-2)) (.leaf (-1))),
  (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_229_2992 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (6))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (7))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (4)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (3))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (6)) (.leaf (1))) (.branch 28 (.leaf (4)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (5))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_2992
  counts := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 10 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-24)) (.leaf (-28)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (-9)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 9 (.leaf (0)) (.branch 31 (.leaf (-5)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-15)) (.leaf (-18)))),
  (.leaf (0))]
  high := ![(.branch 31 (.branch 19 (.leaf (-14)) (.branch 25 (.leaf (-13)) (.leaf (-12)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 30 (.branch 16 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 23 (.leaf (-26)) (.leaf (-25)))) (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.leaf (-11)) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-5)) (.leaf (-3)))),
  (.branch 29 (.branch 27 (.branch 15 (.leaf (-18)) (.leaf (-17))) (.branch 28 (.leaf (-15)) (.leaf (-13)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-9))) (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-5)) (.leaf (-3)))))),
  (.leaf (0))]
def witnessD8_229_2993 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (6)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (7))) (.branch 11 (.leaf (1)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (6)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (3))) (.branch 20 (.leaf (5)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (2))) (.branch 24 (.leaf (6)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (7))) (.branch 28 (.leaf (0)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (4))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (6)) (.leaf (3))))))))
  code := certificateD8_2993
  counts := ![(.branch 15 (.branch 1 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 21 (.leaf (-29)) (.leaf (-31)))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 30 (.branch 22 (.leaf (-31)) (.branch 29 (.leaf (-30)) (.leaf (-25)))) (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5))))),
  (.branch 19 (.branch 5 (.leaf (-14)) (.branch 12 (.leaf (-13)) (.leaf (-12)))) (.branch 26 (.leaf (-11)) (.branch 33 (.leaf (-10)) (.leaf (-5))))),
  (.branch 32 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.leaf (-2)))),
  (.branch 27 (.leaf (-2)) (.branch 28 (.leaf (-1)) (.leaf (0)))),
  (.branch 32 (.branch 23 (.leaf (-7)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 31 (.branch 21 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_229_2994 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (7)) (.branch 16 (.leaf (1)) (.leaf (5))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (4))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (3))) (.branch 28 (.leaf (0)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (7)) (.branch 33 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_2994
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 7 (.leaf (-14)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-19)) (.leaf (-23)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (-4)) (.leaf (-6)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 29 (.leaf (-9)) (.leaf (-13)))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 32 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 24 (.branch 10 (.leaf (-23)) (.branch 17 (.leaf (-22)) (.leaf (-21)))) (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5))))),
  (.branch 27 (.leaf (-6)) (.leaf (-5))),
  (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.branch 33 (.leaf (-10)) (.leaf (-9))))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_229_2995 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (6)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (2))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (7)) (.branch 16 (.leaf (2)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (0))) (.branch 24 (.leaf (6)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (2))) (.branch 28 (.leaf (4)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (1))) (.branch 32 (.leaf (7)) (.branch 33 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_2995
  counts := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-14)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 30 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 31 (.branch 24 (.leaf (-16)) (.branch 30 (.leaf (-15)) (.leaf (-12)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 32 (.branch 26 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 22 (.leaf (-5)) (.branch 28 (.leaf (-4)) (.leaf (-3)))),
  (.branch 32 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 30 (.branch 6 (.leaf (-19)) (.branch 29 (.leaf (-18)) (.leaf (-15)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 23 (.leaf (-2)) (.leaf (0))),
  (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_229_2996 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (2))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (7))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (6))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (4)) (.leaf (2))) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (7))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (4)) (.leaf (1))))))))
  code := certificateD8_2996
  counts := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-24))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 23 (.leaf (-2)) (.branch 29 (.leaf (-1)) (.leaf (0)))),
  (.branch 33 (.leaf (-6)) (.leaf (-3))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (-24)) (.leaf (-23))) (.branch 17 (.leaf (-22)) (.leaf (-21)))) (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5))))),
  (.branch 20 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))),
  (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_229_2997 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (4))) (.branch 3 (.leaf (2)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (6)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (3)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (3)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (7)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (3)) (.leaf (1))))))))
  code := certificateD8_2997
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-23))),
  (.branch 28 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 32 (.branch 27 (.leaf (-15)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 26 (.leaf (-2)) (.leaf (0))),
  (.branch 31 (.branch 21 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.branch 30 (.branch 28 (.leaf (-14)) (.branch 29 (.leaf (-12)) (.leaf (-10)))) (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-23)) (.leaf (-22))) (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19))))) (.branch 19 (.branch 17 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_229_2998 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (5))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (5))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (1)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (7)) (.leaf (1))) (.branch 28 (.leaf (3)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (6))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (1)) (.leaf (2))))))))
  code := certificateD8_2998
  counts := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-28))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (-10)) (.leaf (-11)))),
  (.branch 9 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 31 (.branch 19 (.leaf (-14)) (.branch 25 (.leaf (-13)) (.leaf (-12)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.leaf (-5)) (.branch 28 (.leaf (-4)) (.leaf (-3)))),
  (.branch 23 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 29 (.branch 26 (.branch 3 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-24)) (.branch 28 (.leaf (-21)) (.leaf (-18))))) (.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 32 (.branch 20 (.leaf (-11)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_229_2999 : CycleWitness 8 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (2)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (6))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_2999
  counts := ![(.branch 16 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 25 (.branch 21 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 23 (.leaf (10)) (.leaf (11)))) (.branch 29 (.branch 27 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.leaf (15)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 28 (.leaf (7)) (.branch 31 (.leaf (8)) (.leaf (9)))))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.branch 7 (.leaf (-8)) (.leaf (-9))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-13)) (.leaf (-15)))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (-2)) (.leaf (-4)))),
  (.branch 11 (.leaf (0)) (.leaf (-22))),
  (.branch 22 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 30 (.leaf (-9)) (.leaf (-5))),
  (.branch 32 (.leaf (-6)) (.leaf (-3))),
  (.branch 26 (.branch 22 (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-11))) (.branch 25 (.leaf (-10)) (.leaf (-9))))) (.branch 29 (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 29 (.branch 27 (.branch 9 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.leaf (-2))))),
  (.branch 31 (.leaf (-4)) (.branch 32 (.leaf (-3)) (.leaf (-2)))),
  (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-22)) (.leaf (-21))) (.branch 14 (.leaf (-20)) (.branch 15 (.leaf (-19)) (.leaf (-18))))) (.branch 19 (.branch 17 (.leaf (-17)) (.branch 18 (.leaf (-16)) (.leaf (-15)))) (.branch 20 (.leaf (-14)) (.branch 21 (.leaf (-13)) (.leaf (-12)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-11)) (.leaf (-10))) (.branch 25 (.leaf (-9)) (.branch 26 (.leaf (-8)) (.leaf (-7))))) (.branch 30 (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-5)) (.leaf (-4)))) (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 24 (.branch 23 (.leaf (-11)) (.leaf (-10))) (.branch 25 (.leaf (-9)) (.branch 26 (.leaf (-8)) (.leaf (-7))))) (.branch 30 (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-5)) (.leaf (-4)))) (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_229_3000 : CycleWitness 8 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (6))) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (7)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (4))))))))
  code := certificateD8_3000
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 28 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-26))),
  (.branch 18 (.leaf (0)) (.leaf (-15))),
  (.branch 29 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 29 (.branch 26 (.leaf (-10)) (.leaf (-9))) (.branch 32 (.leaf (-8)) (.leaf (-4)))),
  (.branch 31 (.branch 25 (.leaf (-7)) (.leaf (-6))) (.branch 32 (.leaf (-4)) (.leaf (-2)))),
  (.branch 27 (.leaf (-3)) (.leaf (-2))),
  (.branch 30 (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-5)) (.leaf (-4)))) (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 20 (.branch 13 (.branch 10 (.branch 8 (.leaf (-26)) (.branch 9 (.leaf (-25)) (.leaf (-24)))) (.branch 11 (.leaf (-23)) (.branch 12 (.leaf (-22)) (.leaf (-21))))) (.branch 16 (.branch 14 (.leaf (-20)) (.branch 15 (.leaf (-19)) (.leaf (-18)))) (.branch 18 (.branch 17 (.leaf (-17)) (.leaf (-16))) (.branch 19 (.leaf (-15)) (.leaf (-14)))))) (.branch 26 (.branch 23 (.branch 21 (.leaf (-13)) (.branch 22 (.leaf (-12)) (.leaf (-11)))) (.branch 24 (.leaf (-10)) (.branch 25 (.leaf (-9)) (.leaf (-8))))) (.branch 29 (.branch 27 (.leaf (-7)) (.branch 28 (.leaf (-6)) (.leaf (-5)))) (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 21 (.branch 19 (.leaf (-15)) (.branch 20 (.leaf (-14)) (.leaf (-13)))) (.branch 23 (.branch 22 (.leaf (-12)) (.leaf (-11))) (.branch 24 (.leaf (-10)) (.leaf (-9))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-7))) (.branch 28 (.leaf (-6)) (.leaf (-5)))) (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_229_3001 : CycleWitness 8 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (6)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (7)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (5))) (.branch 23 (.leaf (0)) (.leaf (6))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (3))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (7)) (.leaf (5))))))))
  code := certificateD8_3001
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 28 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.leaf (12)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-25))) (.branch 18 (.leaf (-26)) (.branch 26 (.leaf (-27)) (.leaf (-28))))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 29 (.branch 26 (.leaf (-10)) (.leaf (-9))) (.branch 32 (.leaf (-8)) (.leaf (-4)))),
  (.branch 29 (.branch 27 (.leaf (-28)) (.branch 28 (.leaf (-24)) (.leaf (-20)))) (.branch 31 (.branch 30 (.leaf (-16)) (.leaf (-12))) (.branch 32 (.leaf (-8)) (.leaf (-4))))),
  (.branch 30 (.branch 5 (.leaf (-17)) (.leaf (-16))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-8)) (.leaf (-4))))),
  (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-5)) (.leaf (-4)))) (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 28 (.branch 25 (.branch 8 (.leaf (-19)) (.leaf (-18))) (.branch 26 (.leaf (-16)) (.branch 27 (.leaf (-14)) (.leaf (-12))))) (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-8))) (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 16 (.leaf (-3)) (.leaf (-2)))]
def witnessD8_229_3002 : CycleWitness 8 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (6)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (7)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (5))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (6)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (7))))))))
  code := certificateD8_3002
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 28 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 11 (.leaf (0)) (.branch 27 (.leaf (-11)) (.leaf (-12)))),
  (.branch 16 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 29 (.branch 26 (.leaf (-10)) (.leaf (-9))) (.branch 32 (.leaf (-8)) (.leaf (-4)))),
  (.branch 31 (.branch 25 (.leaf (-7)) (.leaf (-6))) (.branch 32 (.leaf (-4)) (.leaf (-2)))),
  (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 29 (.branch 27 (.leaf (-7)) (.branch 28 (.leaf (-6)) (.leaf (-5)))) (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 24 (.branch 6 (.leaf (-23)) (.branch 23 (.leaf (-22)) (.leaf (-20)))) (.branch 25 (.leaf (-18)) (.branch 26 (.leaf (-16)) (.leaf (-14))))) (.branch 30 (.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-10)) (.leaf (-8)))) (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 30 (.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-10)) (.leaf (-8)))) (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-4)) (.leaf (-2))))),
  (.branch 17 (.leaf (-1)) (.leaf (0)))]
def witnessD8_229_3003 : CycleWitness 8 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (3)) (.leaf (0))) (.branch 19 (.leaf (6)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (7))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_3003
  counts := ![(.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (7)) (.branch 31 (.leaf (8)) (.leaf (9)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-25))),
  (.branch 19 (.leaf (0)) (.leaf (-14))),
  (.branch 30 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 27 (.branch 24 (.leaf (-7)) (.leaf (-6))) (.branch 30 (.leaf (-5)) (.leaf (-4)))),
  (.branch 28 (.leaf (-7)) (.branch 32 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-7))) (.branch 28 (.leaf (-6)) (.leaf (-5)))) (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 29 (.leaf (-5)) (.leaf (-4))) (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 20 (.branch 14 (.branch 11 (.branch 9 (.leaf (-25)) (.branch 10 (.leaf (-24)) (.leaf (-23)))) (.branch 12 (.leaf (-22)) (.branch 13 (.leaf (-21)) (.leaf (-20))))) (.branch 17 (.branch 15 (.leaf (-19)) (.branch 16 (.leaf (-18)) (.leaf (-17)))) (.branch 18 (.leaf (-16)) (.branch 19 (.leaf (-15)) (.leaf (-14)))))) (.branch 26 (.branch 23 (.branch 21 (.leaf (-13)) (.branch 22 (.leaf (-12)) (.leaf (-11)))) (.branch 24 (.leaf (-10)) (.branch 25 (.leaf (-9)) (.leaf (-8))))) (.branch 29 (.branch 27 (.leaf (-7)) (.branch 28 (.leaf (-6)) (.leaf (-5)))) (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 22 (.branch 20 (.leaf (-14)) (.branch 21 (.leaf (-13)) (.leaf (-12)))) (.branch 24 (.branch 23 (.leaf (-11)) (.leaf (-10))) (.branch 25 (.leaf (-9)) (.leaf (-8))))) (.branch 29 (.branch 27 (.leaf (-7)) (.branch 28 (.leaf (-6)) (.leaf (-5)))) (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_229_3004 : CycleWitness 8 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (5))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (6)) (.leaf (0))) (.branch 19 (.leaf (2)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (5))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_3004
  counts := ![(.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (7)) (.branch 31 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 19 (.leaf (-22)) (.leaf (-23)))),
  (.branch 8 (.leaf (0)) (.leaf (-17))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (-21)) (.leaf (-22)))),
  (.branch 14 (.leaf (0)) (.branch 30 (.leaf (-5)) (.leaf (-6)))),
  (.branch 17 (.leaf (0)) (.leaf (-16))),
  (.leaf (0))]
  high := ![(.branch 27 (.branch 24 (.leaf (-7)) (.leaf (-6))) (.branch 30 (.leaf (-5)) (.leaf (-4)))),
  (.branch 28 (.leaf (-7)) (.branch 32 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.branch 20 (.leaf (-23)) (.branch 29 (.leaf (-20)) (.leaf (-16)))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-8)) (.leaf (-4))))),
  (.branch 28 (.branch 26 (.branch 9 (.leaf (-17)) (.leaf (-16))) (.branch 27 (.leaf (-14)) (.leaf (-12)))) (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-8))) (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 27 (.branch 24 (.branch 23 (.leaf (-22)) (.leaf (-20))) (.branch 25 (.leaf (-18)) (.branch 26 (.leaf (-16)) (.leaf (-14))))) (.branch 30 (.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-10)) (.leaf (-8)))) (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (-16)) (.leaf (-15))) (.branch 20 (.leaf (-14)) (.leaf (-13)))) (.branch 23 (.branch 22 (.leaf (-12)) (.leaf (-11))) (.branch 24 (.leaf (-10)) (.leaf (-9))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-7))) (.branch 28 (.leaf (-6)) (.leaf (-5)))) (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_229 : Fin 29 → CycleWitness 8 := ![witnessD8_229_2976, witnessD8_229_2977, witnessD8_229_2978, witnessD8_229_2979, witnessD8_229_2980, witnessD8_229_2981, witnessD8_229_2982, witnessD8_229_2983, witnessD8_229_2984, witnessD8_229_2985, witnessD8_229_2986, witnessD8_229_2987, witnessD8_229_2988, witnessD8_229_2989, witnessD8_229_2990, witnessD8_229_2991, witnessD8_229_2992, witnessD8_229_2993, witnessD8_229_2994, witnessD8_229_2995, witnessD8_229_2996, witnessD8_229_2997, witnessD8_229_2998, witnessD8_229_2999, witnessD8_229_3000, witnessD8_229_3001, witnessD8_229_3002, witnessD8_229_3003, witnessD8_229_3004]
end RealPinwheel.FiveSixths


