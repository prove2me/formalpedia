-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_056
-- name    : RealPinwheel_FiveSixths_WitnessD7_056
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:02:36.991483+00:00
-- url     : https://prove2.me/theorems/3c0fe1c2-7952-42be-a81b-5e0dddc8a27a
-- title:
--   Exact witness block D7_056
-- statement:
--   These exact witnesses represent words 972 through 1001 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 972–1001; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_056_971 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (6)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (5)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (4)) (.leaf (0))) (.branch 28 (.leaf (6)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_971
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (7)) (.branch 31 (.leaf (8)) (.leaf (9)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 33 (.leaf (8)) (.leaf (9)))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 19 (.leaf (-32)) (.leaf (-33)))),
  (.branch 2 (.leaf (0)) (.leaf (-16))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-25))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 28 (.branch 20 (.leaf (-33)) (.branch 24 (.leaf (-31)) (.leaf (-29)))) (.branch 32 (.leaf (-27)) (.branch 33 (.leaf (-18)) (.leaf (-9))))),
  (.branch 22 (.branch 3 (.leaf (-16)) (.leaf (-15))) (.branch 26 (.leaf (-13)) (.branch 30 (.leaf (-11)) (.leaf (-9))))),
  (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.branch 25 (.leaf (-3)) (.leaf (-2))) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 29 (.branch 27 (.branch 4 (.leaf (-25)) (.leaf (-24))) (.branch 28 (.leaf (-21)) (.leaf (-18)))) (.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 21 (.leaf (-8)) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_056_972 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_972
  counts := ![(.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-14)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 14 (.leaf (-8)) (.branch 31 (.leaf (-10)) (.leaf (-11))))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 27 (.leaf (-8)) (.leaf (-9)))),
  (.branch 16 (.leaf (0)) (.leaf (-18))),
  (.branch 33 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 30 (.branch 27 (.leaf (-14)) (.leaf (-13))) (.branch 33 (.leaf (-12)) (.leaf (-6)))),
  (.branch 32 (.leaf (-11)) (.branch 33 (.leaf (-8)) (.leaf (-5)))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 30 (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7)))) (.branch 32 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.leaf (-3))))),
  (.branch 25 (.branch 20 (.branch 18 (.branch 17 (.leaf (-18)) (.leaf (-17))) (.branch 19 (.leaf (-16)) (.leaf (-15)))) (.branch 22 (.branch 21 (.leaf (-14)) (.leaf (-13))) (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_056_973 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (3)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (2))) (.branch 24 (.leaf (1)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (4)) (.leaf (3))) (.branch 28 (.leaf (0)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (6)) (.branch 33 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_973
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-2)) (.leaf (-4)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 26 (.leaf (-11)) (.leaf (-14)))),
  (.branch 15 (.leaf (0)) (.leaf (-19))),
  (.branch 32 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 32 (.leaf (-15)) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 31 (.branch 25 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 28 (.leaf (-4)) (.leaf (-3))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-14)) (.leaf (-13))) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.leaf (-7))))),
  (.branch 24 (.branch 19 (.branch 17 (.branch 16 (.leaf (-19)) (.leaf (-18))) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 21 (.branch 20 (.leaf (-15)) (.leaf (-14))) (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_056_974 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (2))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (1)) (.leaf (5))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (1))) (.branch 24 (.leaf (3)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (5))) (.branch 28 (.leaf (0)) (.leaf (4)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_974
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.leaf (-24))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 32 (.leaf (-15)) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (-24)) (.leaf (-23))) (.branch 17 (.leaf (-22)) (.leaf (-21)))) (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5))))),
  (.branch 20 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))),
  (.branch 33 (.leaf (-4)) (.leaf (-2))),
  (.branch 31 (.branch 21 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_056_975 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (6))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (5)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (2)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (6))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_975
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 25 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 10 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 32 (.branch 27 (.leaf (-15)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 32 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (-2)),
  (.leaf (0)),
  (.branch 33 (.leaf (-2)) (.leaf (-1))),
  (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_056_976 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (6)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (4))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (1))) (.branch 28 (.leaf (6)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (4))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (5)) (.leaf (3))))))))
  code := certificateD7_976
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-7)) (.leaf (-12)))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 31 (.branch 30 (.leaf (-6)) (.leaf (-5))) (.branch 32 (.leaf (-4)) (.branch 33 (.leaf (-3)) (.leaf (-2))))),
  (.branch 33 (.leaf (-3)) (.leaf (-2))),
  (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.leaf (-12)) (.leaf (-11))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_056_977 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (4)) (.leaf (6))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (1)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (6))))))))
  code := certificateD7_977
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 13 (.leaf (-4)) (.branch 30 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-24)) (.leaf (-27)))),
  (.branch 5 (.leaf (0)) (.branch 32 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0))]
  high := ![(.branch 32 (.branch 19 (.leaf (-13)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 32 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 30 (.branch 16 (.leaf (-27)) (.branch 23 (.leaf (-26)) (.leaf (-25)))) (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5))))),
  (.branch 33 (.leaf (-10)) (.leaf (-5))),
  (.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.branch 31 (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (0))]
def witnessD7_056_978 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (5)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (4)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (4)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (6)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (4)) (.leaf (1))))))))
  code := certificateD7_978
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-23))),
  (.branch 28 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 32 (.branch 27 (.leaf (-15)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 26 (.leaf (-2)) (.leaf (0))),
  (.branch 28 (.leaf (-11)) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 31 (.branch 21 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-23)) (.leaf (-22))) (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19))))) (.branch 19 (.branch 17 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_056_979 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (2))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (5)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (4)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (5))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (4))) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (5)) (.leaf (4))))))))
  code := certificateD7_979
  counts := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-14)) (.leaf (-16)))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 32 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 30 (.leaf (-19)) (.leaf (-20)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 31 (.branch 24 (.leaf (-16)) (.branch 30 (.leaf (-15)) (.leaf (-12)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 33 (.leaf (-4)) (.leaf (-3))),
  (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 21 (.branch 14 (.leaf (-3)) (.leaf (-2))) (.branch 28 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-2)),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_056_980 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (4)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (6)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (4)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_980
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-13)) (.leaf (-14)))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-3)))) (.branch 29 (.leaf (-4)) (.branch 33 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-31))),
  (.branch 20 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 32 (.branch 23 (.leaf (-14)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-6)),
  (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.leaf (-4)) (.leaf (-2))),
  (.branch 18 (.branch 10 (.branch 6 (.branch 4 (.leaf (-31)) (.branch 5 (.leaf (-30)) (.leaf (-29)))) (.branch 8 (.branch 7 (.leaf (-28)) (.leaf (-27))) (.branch 9 (.leaf (-26)) (.leaf (-25))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (-24)) (.leaf (-23))) (.branch 13 (.leaf (-22)) (.leaf (-21)))) (.branch 16 (.branch 15 (.leaf (-20)) (.leaf (-19))) (.branch 17 (.leaf (-18)) (.leaf (-17)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (-16)) (.leaf (-15))) (.branch 21 (.leaf (-14)) (.leaf (-13)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-11))) (.branch 25 (.leaf (-10)) (.leaf (-9))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_056_981 : CycleWitness 7 where
  length := 33
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 13 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (6)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (0)))))) (.branch 25 (.branch 20 (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (6))) (.branch 32 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_981
  counts := ![(.branch 15 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))))) (.branch 24 (.branch 19 (.branch 17 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.branch 23 (.leaf (12)) (.leaf (13))))) (.branch 28 (.branch 26 (.leaf (14)) (.leaf (15))) (.branch 30 (.leaf (16)) (.branch 32 (.leaf (17)) (.leaf (18))))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-27))),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 27 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 31 (.leaf (-7)) (.leaf (-6))))),
  (.branch 30 (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-5)) (.leaf (-4)))) (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 26 (.branch 22 (.branch 4 (.leaf (-27)) (.branch 21 (.leaf (-26)) (.leaf (-24)))) (.branch 24 (.branch 23 (.leaf (-22)) (.leaf (-20))) (.branch 25 (.leaf (-18)) (.leaf (-16))))) (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-12)) (.leaf (-10)))) (.branch 31 (.branch 30 (.leaf (-8)) (.leaf (-6))) (.branch 32 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-16)) (.leaf (-14))) (.branch 28 (.leaf (-12)) (.leaf (-10)))) (.branch 31 (.branch 30 (.leaf (-8)) (.leaf (-6))) (.branch 32 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.leaf (-5)) (.branch 32 (.leaf (-4)) (.leaf (-2))))]
def witnessD7_056_982 : CycleWitness 7 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (5))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_982
  counts := ![(.branch 16 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 25 (.branch 20 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 23 (.leaf (10)) (.leaf (11)))) (.branch 29 (.branch 27 (.leaf (12)) (.leaf (13))) (.branch 31 (.leaf (14)) (.leaf (15)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 28 (.leaf (7)) (.branch 32 (.leaf (8)) (.leaf (9)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-6)) (.leaf (-7)))) (.branch 7 (.leaf (-8)) (.branch 9 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-22))),
  (.branch 22 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 32 (.leaf (-10)) (.leaf (-5))),
  (.branch 25 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-3)))),
  (.branch 29 (.branch 27 (.leaf (-7)) (.branch 28 (.leaf (-6)) (.leaf (-5)))) (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-22)) (.leaf (-21))) (.branch 14 (.leaf (-20)) (.branch 15 (.leaf (-19)) (.leaf (-18))))) (.branch 19 (.branch 17 (.leaf (-17)) (.branch 18 (.leaf (-16)) (.leaf (-15)))) (.branch 20 (.leaf (-14)) (.branch 21 (.leaf (-13)) (.leaf (-12)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-11)) (.leaf (-10))) (.branch 25 (.leaf (-9)) (.branch 26 (.leaf (-8)) (.leaf (-7))))) (.branch 30 (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-5)) (.leaf (-4)))) (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 24 (.branch 23 (.leaf (-11)) (.leaf (-10))) (.branch 25 (.leaf (-9)) (.branch 26 (.leaf (-8)) (.leaf (-7))))) (.branch 30 (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-5)) (.leaf (-4)))) (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_056_983 : CycleWitness 7 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (0))) (.branch 19 (.leaf (2)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_983
  counts := ![(.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (7)) (.branch 31 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 19 (.leaf (-22)) (.leaf (-23)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-9))) (.branch 22 (.leaf (-10)) (.branch 30 (.leaf (-11)) (.leaf (-12))))),
  (.branch 8 (.leaf (0)) (.leaf (-17))),
  (.branch 17 (.leaf (0)) (.leaf (-16))),
  (.leaf (0))]
  high := ![(.branch 27 (.branch 24 (.leaf (-7)) (.leaf (-6))) (.branch 30 (.leaf (-5)) (.leaf (-4)))),
  (.branch 28 (.leaf (-7)) (.branch 32 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.branch 20 (.leaf (-23)) (.branch 29 (.leaf (-20)) (.leaf (-16)))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-8)) (.leaf (-4))))),
  (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-8)) (.leaf (-4)))),
  (.branch 28 (.branch 26 (.branch 9 (.leaf (-17)) (.leaf (-16))) (.branch 27 (.leaf (-14)) (.leaf (-12)))) (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-8))) (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (-16)) (.leaf (-15))) (.branch 20 (.leaf (-14)) (.leaf (-13)))) (.branch 23 (.branch 22 (.leaf (-12)) (.leaf (-11))) (.branch 24 (.leaf (-10)) (.leaf (-9))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-7))) (.branch 28 (.leaf (-6)) (.leaf (-5)))) (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_056_984 : CycleWitness 7 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (6)) (.leaf (0))) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_984
  counts := ![(.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (-21)) (.leaf (-22)))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 27 (.branch 24 (.leaf (-7)) (.leaf (-6))) (.branch 30 (.leaf (-5)) (.leaf (-4)))),
  (.branch 31 (.branch 25 (.leaf (-7)) (.leaf (-6))) (.branch 32 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.leaf (-5)) (.branch 32 (.leaf (-4)) (.leaf (-2)))),
  (.branch 30 (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-5)) (.leaf (-4)))) (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 24 (.branch 23 (.leaf (-22)) (.leaf (-20))) (.branch 25 (.leaf (-18)) (.branch 26 (.leaf (-16)) (.leaf (-14))))) (.branch 30 (.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-10)) (.leaf (-8)))) (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 30 (.branch 12 (.leaf (-11)) (.branch 29 (.leaf (-10)) (.leaf (-8)))) (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD7_056_985 : CycleWitness 7 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (3))) (.branch 23 (.leaf (1)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (2))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (6)) (.leaf (3))))))))
  code := certificateD7_985
  counts := ![(.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 27 (.leaf (9)) (.branch 31 (.leaf (10)) (.leaf (11)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-18)) (.leaf (-26)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 30 (.leaf (-14)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (-17)) (.leaf (-18)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 28 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 7 (.leaf (-26)) (.branch 24 (.leaf (-25)) (.leaf (-23)))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-13)) (.leaf (-8))))),
  (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-13)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 30 (.branch 6 (.leaf (-6)) (.branch 29 (.leaf (-5)) (.leaf (-4)))) (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-16))) (.branch 27 (.leaf (-14)) (.leaf (-12)))) (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-8))) (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (-2))]
def witnessD7_056_986 : CycleWitness 7 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (6)) (.leaf (0))) (.branch 19 (.leaf (3)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (4))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (5))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (6))))))))
  code := certificateD7_986
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-23)) (.leaf (-26)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-17)) (.leaf (-26)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-18))) (.branch 29 (.leaf (-19)) (.leaf (-20)))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 32 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 15 (.branch 5 (.leaf (-26)) (.leaf (-25))) (.branch 25 (.leaf (-24)) (.branch 32 (.leaf (-20)) (.leaf (-10))))),
  (.branch 26 (.branch 16 (.leaf (-26)) (.branch 21 (.leaf (-25)) (.leaf (-24)))) (.branch 31 (.leaf (-23)) (.branch 32 (.leaf (-17)) (.leaf (-11))))),
  (.branch 31 (.branch 30 (.leaf (-20)) (.leaf (-15))) (.branch 32 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (-3)),
  (.branch 27 (.branch 24 (.branch 6 (.leaf (-23)) (.branch 23 (.leaf (-22)) (.leaf (-20)))) (.branch 25 (.leaf (-18)) (.branch 26 (.leaf (-16)) (.leaf (-14))))) (.branch 30 (.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-10)) (.leaf (-8)))) (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 29 (.branch 27 (.branch 10 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-12)) (.leaf (-10)))) (.branch 31 (.branch 30 (.leaf (-8)) (.leaf (-6))) (.branch 32 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD7_056_987 : CycleWitness 7 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (1)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (3))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (6))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_987
  counts := ![(.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (7)) (.branch 31 (.leaf (8)) (.leaf (9)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-9)) (.leaf (-11)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 19 (.leaf (-14)) (.leaf (-24)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (-12)) (.leaf (-14)))),
  (.branch 16 (.leaf (0)) (.branch 30 (.leaf (-2)) (.leaf (-6))))]
  high := ![(.branch 27 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.leaf (-8)))),
  (.branch 24 (.branch 20 (.leaf (-24)) (.leaf (-23))) (.branch 28 (.leaf (-22)) (.branch 32 (.leaf (-21)) (.leaf (-15))))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-7))) (.branch 28 (.leaf (-6)) (.leaf (-5)))) (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 9 (.leaf (-5)) (.branch 23 (.leaf (-4)) (.leaf (-3)))) (.branch 25 (.leaf (-2)) (.branch 26 (.leaf (-1)) (.leaf (0))))),
  (.branch 30 (.branch 12 (.leaf (-11)) (.branch 29 (.leaf (-10)) (.leaf (-8)))) (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-4)) (.leaf (-2))))),
  (.branch 26 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 24 (.leaf (-11)) (.branch 25 (.leaf (-10)) (.leaf (-9))))) (.branch 29 (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4))))]
def witnessD7_056_988 : CycleWitness 7 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (3))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (6)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_988
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 26 (.leaf (-18)) (.leaf (-22)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))) (.branch 14 (.leaf (-9)) (.branch 18 (.leaf (-10)) (.leaf (-11))))),
  (.branch 3 (.leaf (0)) (.branch 19 (.leaf (-13)) (.leaf (-17)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (-23)) (.leaf (-24)))),
  (.branch 13 (.leaf (0)) (.branch 29 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 31 (.branch 27 (.leaf (-22)) (.leaf (-21))) (.branch 32 (.leaf (-16)) (.leaf (-11)))),
  (.branch 19 (.leaf (-11)) (.branch 28 (.leaf (-10)) (.leaf (-8)))),
  (.branch 26 (.branch 20 (.leaf (-17)) (.leaf (-15))) (.branch 32 (.leaf (-13)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 30 (.branch 29 (.leaf (-5)) (.leaf (-4))) (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-24)) (.branch 23 (.leaf (-22)) (.leaf (-20)))) (.branch 25 (.leaf (-18)) (.branch 26 (.leaf (-16)) (.leaf (-14))))) (.branch 30 (.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-10)) (.leaf (-8)))) (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 31 (.branch 30 (.leaf (-8)) (.leaf (-6))) (.branch 32 (.leaf (-4)) (.leaf (-2))))]
def witnessD7_056_989 : CycleWitness 7 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (6))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (6)) (.leaf (4))))))))
  code := certificateD7_989
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-21)) (.leaf (-22)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-9))) (.branch 22 (.leaf (-10)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 31 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 32 (.leaf (-6)) (.leaf (-3)))),
  (.branch 31 (.branch 30 (.leaf (-8)) (.leaf (-6))) (.branch 32 (.leaf (-4)) (.leaf (-2)))),
  (.branch 30 (.branch 12 (.leaf (-22)) (.branch 29 (.leaf (-20)) (.leaf (-16)))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-8)) (.leaf (-4))))),
  (.branch 23 (.leaf (-11)) (.branch 32 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 30 (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-5)) (.leaf (-4)))) (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_056_990 : CycleWitness 7 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (4))) (.branch 15 (.leaf (2)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (2))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (4))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_990
  counts := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 19 (.leaf (-22)) (.branch 27 (.leaf (-23)) (.leaf (-24))))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-8))) (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-4)) (.leaf (-2))))),
  (.branch 31 (.branch 30 (.leaf (-8)) (.leaf (-6))) (.branch 32 (.leaf (-4)) (.leaf (-2)))),
  (.branch 27 (.leaf (-3)) (.leaf (-2))),
  (.branch 30 (.branch 28 (.leaf (-24)) (.branch 29 (.leaf (-20)) (.leaf (-16)))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-8)) (.leaf (-4))))),
  (.branch 31 (.branch 6 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-8)) (.leaf (-4)))),
  (.branch 17 (.leaf (-2)) (.leaf (0))),
  (.branch 32 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_056_991 : CycleWitness 7 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (6))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_991
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 28 (.leaf (7)) (.branch 32 (.leaf (8)) (.leaf (9)))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-27))),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 31 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 32 (.leaf (-6)) (.leaf (-3)))),
  (.branch 25 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-3)))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1)))),
  (.branch 26 (.branch 22 (.branch 4 (.leaf (-27)) (.branch 21 (.leaf (-26)) (.leaf (-24)))) (.branch 24 (.branch 23 (.leaf (-22)) (.leaf (-20))) (.branch 25 (.leaf (-18)) (.leaf (-16))))) (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-12)) (.leaf (-10)))) (.branch 31 (.branch 30 (.leaf (-8)) (.leaf (-6))) (.branch 32 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-16)) (.leaf (-14))) (.branch 28 (.leaf (-12)) (.leaf (-10)))) (.branch 31 (.branch 30 (.leaf (-8)) (.leaf (-6))) (.branch 32 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.leaf (-5)) (.branch 32 (.leaf (-4)) (.leaf (-2))))]
def witnessD7_056_992 : CycleWitness 7 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (3)) (.leaf (0))) (.branch 19 (.leaf (2)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_992
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 7 (.leaf (-22)) (.branch 10 (.leaf (-27)) (.leaf (-32))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 25 (.leaf (-4)) (.branch 29 (.leaf (-5)) (.leaf (-6))))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (-2)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (-17)) (.leaf (-21)))),
  (.branch 12 (.leaf (0)) (.branch 28 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 23 (.branch 15 (.branch 11 (.leaf (-32)) (.leaf (-31))) (.branch 19 (.leaf (-30)) (.leaf (-29)))) (.branch 31 (.branch 27 (.leaf (-28)) (.leaf (-27))) (.branch 32 (.leaf (-21)) (.leaf (-15))))),
  (.branch 31 (.branch 30 (.leaf (-6)) (.leaf (-5))) (.branch 32 (.leaf (-4)) (.leaf (-3)))),
  (.branch 20 (.leaf (-2)) (.branch 28 (.leaf (-1)) (.leaf (0)))),
  (.branch 24 (.leaf (-9)) (.leaf (-8))),
  (.branch 32 (.leaf (-2)) (.leaf (-1))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-21)) (.leaf (-19))) (.branch 27 (.leaf (-17)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-13)) (.leaf (-11))) (.branch 31 (.leaf (-9)) (.branch 32 (.leaf (-7)) (.leaf (-5)))))),
  (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-8))) (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-4)) (.leaf (-2)))))]
def witnessD7_056_993 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 5 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 13 (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (6)))))) (.branch 24 (.branch 21 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 29 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (5)))))))
  code := certificateD7_993
  counts := ![(.branch 15 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 10 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 12 (.leaf (7)) (.branch 13 (.leaf (8)) (.leaf (9)))))) (.branch 23 (.branch 18 (.branch 17 (.leaf (10)) (.leaf (11))) (.branch 20 (.leaf (12)) (.branch 21 (.leaf (13)) (.leaf (14))))) (.branch 28 (.branch 25 (.leaf (15)) (.branch 26 (.leaf (16)) (.leaf (17)))) (.branch 29 (.leaf (18)) (.branch 31 (.leaf (19)) (.leaf (20))))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-24))),
  (.branch 24 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 16 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 30 (.leaf (-7)) (.leaf (-5))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.branch 14 (.branch 11 (.branch 9 (.leaf (-24)) (.branch 10 (.leaf (-23)) (.leaf (-22)))) (.branch 12 (.leaf (-21)) (.branch 13 (.leaf (-20)) (.leaf (-19))))) (.branch 17 (.branch 15 (.leaf (-18)) (.branch 16 (.leaf (-17)) (.leaf (-16)))) (.branch 18 (.leaf (-15)) (.branch 19 (.leaf (-14)) (.leaf (-13)))))) (.branch 26 (.branch 23 (.branch 21 (.leaf (-12)) (.branch 22 (.leaf (-11)) (.leaf (-10)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-13)))) (.branch 22 (.branch 21 (.leaf (-12)) (.leaf (-11))) (.branch 23 (.leaf (-10)) (.leaf (-9))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_056_994 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 5 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 13 (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.leaf (5)) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 21 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 29 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (6)) (.branch 31 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_994
  counts := ![(.branch 15 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 10 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 12 (.leaf (7)) (.branch 13 (.leaf (8)) (.leaf (9)))))) (.branch 23 (.branch 18 (.branch 17 (.leaf (10)) (.leaf (11))) (.branch 20 (.leaf (12)) (.branch 21 (.leaf (13)) (.leaf (14))))) (.branch 28 (.branch 25 (.leaf (15)) (.branch 26 (.leaf (16)) (.leaf (17)))) (.branch 29 (.leaf (18)) (.branch 31 (.leaf (19)) (.leaf (20))))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.leaf (-18))),
  (.branch 30 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 30 (.leaf (-7)) (.leaf (-5))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 23 (.branch 18 (.branch 16 (.branch 15 (.leaf (-18)) (.leaf (-17))) (.branch 17 (.leaf (-16)) (.leaf (-15)))) (.branch 20 (.branch 19 (.leaf (-14)) (.leaf (-13))) (.branch 21 (.leaf (-12)) (.branch 22 (.leaf (-11)) (.leaf (-10)))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_056_995 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (5))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (6)) (.leaf (1)))))))
  code := certificateD7_995
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 20 (.leaf (9)) (.leaf (10)))) (.branch 28 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 29 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.leaf (12)))))),
  (.branch 10 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))) (.branch 18 (.leaf (-16)) (.branch 20 (.leaf (-18)) (.leaf (-20))))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-26))),
  (.branch 15 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-10))),
  (.branch 31 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 26 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.leaf (-13)))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 12 (.branch 9 (.branch 7 (.leaf (-26)) (.branch 8 (.leaf (-25)) (.leaf (-24)))) (.branch 10 (.leaf (-23)) (.branch 11 (.leaf (-22)) (.leaf (-21))))) (.branch 15 (.branch 13 (.leaf (-20)) (.branch 14 (.leaf (-19)) (.leaf (-18)))) (.branch 17 (.branch 16 (.leaf (-17)) (.leaf (-16))) (.branch 18 (.leaf (-15)) (.leaf (-14)))))) (.branch 25 (.branch 22 (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))) (.branch 23 (.leaf (-10)) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (-17)) (.leaf (-16))) (.branch 18 (.leaf (-15)) (.leaf (-14)))) (.branch 21 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 22 (.leaf (-11)) (.leaf (-10))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_056_996 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_996
  counts := ![(.branch 15 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 22 (.branch 18 (.branch 17 (.leaf (8)) (.leaf (9))) (.branch 20 (.leaf (10)) (.leaf (11)))) (.branch 26 (.branch 24 (.leaf (12)) (.leaf (13))) (.branch 28 (.leaf (14)) (.branch 31 (.leaf (15)) (.leaf (16))))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-21))),
  (.branch 27 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-21)) (.leaf (-20))) (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17))))) (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_056_997 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (6)) (.leaf (1)))))))
  code := certificateD7_997
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 20 (.leaf (9)) (.leaf (10)))) (.branch 28 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))) (.branch 18 (.leaf (-16)) (.branch 20 (.leaf (-18)) (.leaf (-20))))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 15 (.leaf (0)) (.leaf (-17))),
  (.branch 31 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 26 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.leaf (-13)))),
  (.branch 23 (.leaf (-2)) (.leaf (0))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (-17)) (.leaf (-16))) (.branch 18 (.leaf (-15)) (.leaf (-14)))) (.branch 21 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 22 (.leaf (-11)) (.leaf (-10))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_056_998 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_998
  counts := ![(.branch 15 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 23 (.branch 18 (.branch 17 (.leaf (8)) (.leaf (9))) (.branch 20 (.leaf (10)) (.leaf (11)))) (.branch 27 (.branch 25 (.leaf (12)) (.leaf (13))) (.branch 29 (.leaf (14)) (.branch 31 (.leaf (15)) (.leaf (16))))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (-5))) (.branch 26 (.leaf (-6)) (.leaf (-7)))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-20))),
  (.branch 28 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 21 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.leaf (-8)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.branch 27 (.leaf (-7)) (.branch 28 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.leaf (-4)) (.branch 31 (.leaf (-3)) (.leaf (-2))))),
  (.branch 11 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 17 (.branch 14 (.branch 13 (.leaf (-20)) (.leaf (-19))) (.branch 15 (.leaf (-18)) (.branch 16 (.leaf (-17)) (.leaf (-16))))) (.branch 19 (.branch 18 (.leaf (-15)) (.leaf (-14))) (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_056_999 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (6)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (0))) (.branch 31 (.leaf (3)) (.leaf (1)))))))
  code := certificateD7_999
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 17 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 27 (.branch 24 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 18 (.leaf (-18)) (.leaf (-22)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 9 (.leaf (-2)) (.branch 12 (.leaf (-3)) (.leaf (-4))))),
  (.branch 4 (.leaf (0)) (.leaf (-20))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-2)) (.leaf (-4)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-25))),
  (.branch 23 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 25 (.branch 19 (.leaf (-22)) (.branch 22 (.leaf (-21)) (.leaf (-20)))) (.branch 28 (.leaf (-19)) (.branch 31 (.leaf (-18)) (.leaf (-13))))),
  (.branch 29 (.leaf (-4)) (.leaf (0))),
  (.branch 28 (.branch 16 (.branch 5 (.leaf (-20)) (.leaf (-19))) (.branch 27 (.leaf (-18)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3))))),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.branch 13 (.branch 10 (.branch 8 (.leaf (-25)) (.branch 9 (.leaf (-24)) (.leaf (-23)))) (.branch 11 (.leaf (-22)) (.branch 12 (.leaf (-21)) (.leaf (-20))))) (.branch 16 (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17)))) (.branch 17 (.leaf (-16)) (.branch 18 (.leaf (-15)) (.leaf (-14)))))) (.branch 25 (.branch 22 (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))) (.branch 23 (.leaf (-10)) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_056_1000 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (6))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (1)))))))
  code := certificateD7_1000
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 17 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 27 (.branch 24 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 18 (.leaf (-18)) (.leaf (-22)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 28 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 13 (.leaf (0)) (.leaf (-19))),
  (.branch 29 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-26))),
  (.branch 22 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 25 (.branch 19 (.leaf (-22)) (.branch 22 (.leaf (-21)) (.leaf (-20)))) (.branch 28 (.leaf (-19)) (.branch 31 (.leaf (-18)) (.leaf (-13))))),
  (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-3)) (.leaf (0)))),
  (.branch 26 (.leaf (-5)) (.leaf (-3))),
  (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-19)) (.leaf (-18))) (.branch 16 (.leaf (-17)) (.leaf (-16)))) (.branch 19 (.branch 18 (.leaf (-15)) (.leaf (-14))) (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.branch 12 (.branch 9 (.branch 7 (.leaf (-26)) (.branch 8 (.leaf (-25)) (.leaf (-24)))) (.branch 10 (.leaf (-23)) (.branch 11 (.leaf (-22)) (.leaf (-21))))) (.branch 15 (.branch 13 (.leaf (-20)) (.branch 14 (.leaf (-19)) (.leaf (-18)))) (.branch 17 (.branch 16 (.leaf (-17)) (.leaf (-16))) (.branch 18 (.leaf (-15)) (.leaf (-14)))))) (.branch 25 (.branch 22 (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))) (.branch 23 (.leaf (-10)) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_056 : Fin 30 → CycleWitness 7 := ![witnessD7_056_971, witnessD7_056_972, witnessD7_056_973, witnessD7_056_974, witnessD7_056_975, witnessD7_056_976, witnessD7_056_977, witnessD7_056_978, witnessD7_056_979, witnessD7_056_980, witnessD7_056_981, witnessD7_056_982, witnessD7_056_983, witnessD7_056_984, witnessD7_056_985, witnessD7_056_986, witnessD7_056_987, witnessD7_056_988, witnessD7_056_989, witnessD7_056_990, witnessD7_056_991, witnessD7_056_992, witnessD7_056_993, witnessD7_056_994, witnessD7_056_995, witnessD7_056_996, witnessD7_056_997, witnessD7_056_998, witnessD7_056_999, witnessD7_056_1000]
end RealPinwheel.FiveSixths


