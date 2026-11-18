-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_013
-- name    : RealPinwheel_FiveSixths_WitnessD6_013
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:42:24.886388+00:00
-- url     : https://prove2.me/theorems/a21f273a-1619-422d-8d9d-2106e3ebd7d3
-- title:
--   Exact witness block D6_013
-- statement:
--   These exact witnesses represent words 373 through 420 of source certificate file D6. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D6, entries 373–420; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D6.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD6
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD6_013_372 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (1)) (.leaf (4)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (5)) (.branch 15 (.leaf (1)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (4)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_372
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-12)) (.leaf (-13)))),
  (.branch 16 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 10 (.branch 2 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 14 (.leaf (-11)) (.branch 18 (.leaf (-10)) (.leaf (-9))))),
  (.branch 16 (.leaf (-13)) (.branch 21 (.leaf (-10)) (.leaf (-5)))),
  (.branch 17 (.leaf (-3)) (.leaf (0))),
  (.branch 19 (.branch 11 (.leaf (-14)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_013_373 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (2)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (5))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (4)) (.branch 21 (.leaf (3)) (.leaf (1)))))))
  code := certificateD6_373
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-16))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 15 (.leaf (-2)) (.branch 19 (.leaf (-1)) (.leaf (0)))),
  (.branch 19 (.branch 3 (.leaf (-16)) (.branch 18 (.leaf (-15)) (.leaf (-12)))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.leaf (-5)) (.leaf (-3))),
  (.branch 21 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_013_374 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (4)) (.leaf (2)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (4))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (5))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (4)) (.leaf (1)))))))
  code := certificateD6_374
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-1)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 11 (.branch 2 (.leaf (-17)) (.leaf (-16))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-10)) (.leaf (-5))))),
  (.branch 13 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (0)))),
  (.branch 9 (.branch 3 (.leaf (-11)) (.leaf (-10))) (.branch 15 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-5))))),
  (.branch 19 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.leaf (-4)) (.leaf (-3))),
  (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_013_375 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (1)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (5)) (.leaf (3)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (2)) (.leaf (4)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (5)) (.branch 15 (.leaf (1)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (3)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (2)) (.leaf (5)))))))
  code := certificateD6_375
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 19 (.branch 18 (.leaf (-10)) (.leaf (-8))) (.branch 20 (.leaf (-6)) (.branch 21 (.leaf (-4)) (.leaf (-2))))),
  (.branch 21 (.leaf (-4)) (.leaf (-2))),
  (.leaf (-2)),
  (.branch 20 (.branch 14 (.leaf (-7)) (.leaf (-6))) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 15 (.leaf (-2)) (.leaf (0)))]
def witnessD6_013_376 : CycleWitness 6 where
  length := 21
  word := (.branch 11 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (4)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (5)) (.branch 20 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_376
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 15 (.branch 11 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))) (.branch 18 (.branch 16 (.leaf (9)) (.leaf (10))) (.branch 20 (.leaf (11)) (.leaf (12)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-16))),
  (.branch 12 (.leaf (0)) (.leaf (-9))),
  (.branch 19 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 17 (.leaf (-6)) (.branch 19 (.leaf (-5)) (.leaf (-4)))),
  (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-16)) (.leaf (-15))) (.branch 8 (.leaf (-14)) (.leaf (-13)))) (.branch 11 (.branch 10 (.leaf (-12)) (.leaf (-11))) (.branch 12 (.leaf (-10)) (.leaf (-9))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-9)) (.leaf (-8))) (.branch 15 (.leaf (-7)) (.leaf (-6)))) (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_013_377 : CycleWitness 6 where
  length := 21
  word := (.branch 11 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (4)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (0))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_377
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 15 (.branch 11 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))) (.branch 18 (.branch 16 (.leaf (9)) (.leaf (10))) (.branch 20 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 17 (.leaf (-6)) (.branch 19 (.leaf (-5)) (.leaf (-4)))),
  (.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.branch 15 (.branch 4 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-12)) (.leaf (-10)))) (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-6))) (.branch 20 (.leaf (-4)) (.leaf (-2))))),
  (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-6))) (.branch 20 (.leaf (-4)) (.leaf (-2)))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.branch 14 (.leaf (-8)) (.leaf (-7))))) (.branch 18 (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-5)) (.leaf (-4)))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_013_378 : CycleWitness 6 where
  length := 21
  word := (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 8 (.branch 7 (.leaf (3)) (.leaf (0))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (0)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 17 (.leaf (5)) (.leaf (0))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_378
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 16 (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))) (.branch 18 (.leaf (9)) (.branch 20 (.leaf (10)) (.leaf (11)))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-10)) (.leaf (-20)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-19)))),
  (.branch 17 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 11 (.branch 5 (.branch 3 (.leaf (-20)) (.leaf (-19))) (.branch 7 (.leaf (-18)) (.branch 9 (.leaf (-17)) (.leaf (-16))))) (.branch 15 (.branch 13 (.leaf (-15)) (.leaf (-14))) (.branch 17 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))))),
  (.branch 12 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 4 (.leaf (-8)) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.leaf (-2))))),
  (.branch 10 (.branch 8 (.leaf (-6)) (.branch 9 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.branch 11 (.leaf (-3)) (.leaf (-2))) (.branch 13 (.leaf (-1)) (.leaf (0))))),
  (.branch 17 (.branch 15 (.branch 14 (.leaf (-19)) (.leaf (-18))) (.branch 16 (.leaf (-17)) (.leaf (-16)))) (.branch 19 (.branch 18 (.leaf (-15)) (.leaf (-14))) (.branch 20 (.leaf (-13)) (.leaf (-12))))),
  (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_013_379 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (3)))))))
  code := certificateD6_379
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 19 (.leaf (8)) (.leaf (9)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-13)))),
  (.branch 20 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 20 (.leaf (-6)) (.leaf (-3))),
  (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 17 (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10)))) (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6))))),
  (.leaf (-1))]
def witnessD6_013_380 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_380
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-6)))),
  (.branch 11 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 18 (.leaf (-5)) (.leaf (-3))),
  (.branch 19 (.branch 10 (.leaf (-12)) (.leaf (-11))) (.branch 20 (.leaf (-8)) (.leaf (-5)))),
  (.branch 5 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 17 (.leaf (-6)) (.leaf (-5))) (.branch 19 (.leaf (-4)) (.branch 20 (.leaf (-3)) (.leaf (-2))))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-10)) (.leaf (-9))) (.branch 14 (.leaf (-8)) (.branch 15 (.leaf (-7)) (.leaf (-6))))) (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_013_381 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (4)))))))
  code := certificateD6_381
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 6 (.leaf (-18)) (.leaf (-21)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 12 (.leaf (-2)) (.branch 20 (.leaf (-3)) (.leaf (-5))))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 15 (.branch 7 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19)))) (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-14)) (.leaf (-10))))),
  (.branch 3 (.leaf (-11)) (.branch 20 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (-5)),
  (.branch 18 (.branch 6 (.leaf (-11)) (.branch 17 (.leaf (-10)) (.leaf (-8)))) (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-4)) (.leaf (-2))))),
  (.branch 10 (.leaf (-2)) (.branch 11 (.leaf (-1)) (.leaf (0)))),
  (.branch 17 (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_013_382 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (2)))))))
  code := certificateD6_382
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 19 (.leaf (8)) (.leaf (9)))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 16 (.leaf (-6)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-12))),
  (.branch 20 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 20 (.leaf (-6)) (.leaf (-3))),
  (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 12 (.branch 10 (.leaf (-12)) (.branch 11 (.leaf (-11)) (.leaf (-10)))) (.branch 13 (.leaf (-9)) (.branch 14 (.leaf (-8)) (.leaf (-7))))) (.branch 18 (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-5)) (.leaf (-4)))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_013_383 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (5)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_383
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 11 (.leaf (0)) (.leaf (-10))),
  (.branch 18 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 18 (.leaf (-5)) (.leaf (-3))),
  (.branch 20 (.leaf (-4)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-17)) (.leaf (-16))) (.branch 7 (.leaf (-15)) (.leaf (-14)))) (.branch 10 (.branch 9 (.leaf (-13)) (.leaf (-12))) (.branch 11 (.leaf (-11)) (.leaf (-10))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-9)) (.leaf (-8))) (.branch 15 (.leaf (-7)) (.leaf (-6)))) (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-10)) (.leaf (-9))) (.branch 14 (.leaf (-8)) (.branch 15 (.leaf (-7)) (.leaf (-6))))) (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_013_384 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (2)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (4)))))))
  code := certificateD6_384
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 8 (.leaf (-10)) (.branch 10 (.leaf (-12)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 17 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 14 (.branch 11 (.leaf (-15)) (.leaf (-14))) (.branch 17 (.leaf (-13)) (.branch 20 (.leaf (-12)) (.leaf (-8))))),
  (.branch 3 (.leaf (-9)) (.branch 16 (.leaf (-8)) (.leaf (-5)))),
  (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-12)) (.leaf (-10)))) (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-6))) (.branch 20 (.leaf (-4)) (.leaf (-2))))),
  (.branch 10 (.leaf (-2)) (.branch 11 (.leaf (-1)) (.leaf (0)))),
  (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_013_385 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_385
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 12 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-10)))),
  (.leaf (0))]
  high := ![(.branch 18 (.leaf (-5)) (.leaf (-3))),
  (.branch 19 (.branch 13 (.leaf (-15)) (.leaf (-12))) (.branch 20 (.leaf (-8)) (.leaf (-4)))),
  (.branch 12 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-12)) (.leaf (-10)))) (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-6))) (.branch 20 (.leaf (-4)) (.leaf (-2))))),
  (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))),
  (.leaf (0))]
def witnessD6_013_386 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (2)))))))
  code := certificateD6_386
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 16 (.leaf (-6)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-8)) (.leaf (-14)))),
  (.branch 20 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 12 (.branch 4 (.leaf (-18)) (.leaf (-17))) (.branch 20 (.leaf (-16)) (.leaf (-8)))),
  (.branch 19 (.branch 3 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4))))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6)))))),
  (.leaf (-1))]
def witnessD6_013_387 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (4)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (2)))))))
  code := certificateD6_387
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 10 (.leaf (-12)) (.branch 14 (.leaf (-13)) (.leaf (-14))))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.leaf (-14)) (.branch 20 (.leaf (-10)) (.leaf (-5)))),
  (.branch 6 (.leaf (-1)) (.leaf (0))),
  (.branch 9 (.leaf (-3)) (.leaf (-2))),
  (.branch 18 (.branch 5 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4))))),
  (.branch 17 (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_013_388 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (5))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (4)))))))
  code := certificateD6_388
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 5 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.leaf (-4)) (.leaf (-2))),
  (.branch 19 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.leaf (-4)) (.branch 20 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 14 (.branch 10 (.branch 8 (.leaf (-14)) (.branch 9 (.leaf (-13)) (.leaf (-12)))) (.branch 12 (.branch 11 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.leaf (-8))))) (.branch 17 (.branch 15 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_013_389 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (4)))))))
  code := certificateD6_389
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-4)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))),
  (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 15 (.branch 12 (.branch 10 (.leaf (-12)) (.branch 11 (.leaf (-11)) (.leaf (-10)))) (.branch 13 (.leaf (-9)) (.branch 14 (.leaf (-8)) (.leaf (-7))))) (.branch 18 (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-5)) (.leaf (-4)))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_013_390 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (3)))))))
  code := certificateD6_390
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 18 (.leaf (-8)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-6)) (.leaf (-8)))),
  (.branch 20 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.leaf (-11)) (.branch 20 (.leaf (-8)) (.leaf (-5)))),
  (.branch 18 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.branch 16 (.leaf (-1)) (.leaf (0))))),
  (.branch 17 (.branch 15 (.leaf (-8)) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-1))]
def witnessD6_013_391 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (2)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (4)))))))
  code := certificateD6_391
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 19 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 18 (.leaf (-8)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 20 (.leaf (-9)) (.leaf (-6))),
  (.branch 16 (.leaf (-6)) (.leaf (-5))),
  (.branch 19 (.leaf (-10)) (.branch 20 (.leaf (-7)) (.leaf (-4)))),
  (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 13 (.branch 9 (.branch 7 (.leaf (-15)) (.branch 8 (.leaf (-14)) (.leaf (-13)))) (.branch 11 (.branch 10 (.leaf (-12)) (.leaf (-11))) (.branch 12 (.leaf (-10)) (.leaf (-9))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_013_392 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (2)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (2)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_392
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-9)))),
  (.branch 10 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 9 (.leaf (-5)) (.branch 20 (.leaf (-4)) (.leaf (-2)))),
  (.branch 7 (.leaf (-8)) (.branch 16 (.leaf (-7)) (.leaf (-5)))),
  (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-6)) (.leaf (-4)))),
  (.branch 8 (.leaf (-2)) (.branch 18 (.leaf (-1)) (.leaf (0)))),
  (.branch 17 (.branch 15 (.branch 14 (.leaf (-9)) (.leaf (-8))) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.leaf (-2))))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.branch 14 (.leaf (-8)) (.leaf (-7))))) (.branch 18 (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-5)) (.leaf (-4)))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_013_393 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (5))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (4)))))))
  code := certificateD6_393
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-12)))) (.branch 14 (.leaf (-13)) (.branch 18 (.leaf (-14)) (.leaf (-15))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 16 (.leaf (-5)) (.branch 20 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.leaf (-15)) (.branch 20 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (-4)),
  (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 14 (.branch 10 (.branch 8 (.leaf (-14)) (.branch 9 (.leaf (-13)) (.leaf (-12)))) (.branch 12 (.branch 11 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.leaf (-8))))) (.branch 17 (.branch 15 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_013_394 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (2)))))))
  code := certificateD6_394
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 12 (.leaf (-10)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.branch 13 (.leaf (-12)) (.leaf (-10))) (.branch 20 (.leaf (-7)) (.leaf (-4)))),
  (.leaf (0)),
  (.leaf (-4)),
  (.branch 17 (.branch 4 (.leaf (-8)) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.leaf (-2))))),
  (.branch 15 (.branch 12 (.branch 10 (.leaf (-12)) (.branch 11 (.leaf (-11)) (.leaf (-10)))) (.branch 13 (.leaf (-9)) (.branch 14 (.leaf (-8)) (.leaf (-7))))) (.branch 18 (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-5)) (.leaf (-4)))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_013_395 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (5))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (1)) (.leaf (4)))))))
  code := certificateD6_395
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 9 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-10)) (.leaf (-14)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 13 (.leaf (-6)) (.leaf (-7)))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 19 (.branch 10 (.leaf (-18)) (.leaf (-15))) (.branch 20 (.leaf (-10)) (.leaf (-5)))),
  (.branch 12 (.leaf (-8)) (.leaf (-5))),
  (.branch 18 (.branch 7 (.leaf (-14)) (.leaf (-13))) (.branch 19 (.leaf (-10)) (.branch 20 (.leaf (-7)) (.leaf (-4))))),
  (.branch 14 (.leaf (-7)) (.branch 20 (.leaf (-6)) (.leaf (-4)))),
  (.branch 11 (.leaf (-1)) (.leaf (0))),
  (.branch 18 (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-5)) (.leaf (-4)))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_013_396 : CycleWitness 6 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (5)) (.leaf (1)))))))
  code := certificateD6_396
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 9 (.leaf (-17)) (.branch 13 (.leaf (-18)) (.leaf (-19))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 14 (.leaf (-7)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-7)))),
  (.branch 20 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 19 (.branch 14 (.leaf (-19)) (.leaf (-15))) (.branch 20 (.leaf (-10)) (.leaf (-5)))),
  (.branch 13 (.leaf (-3)) (.leaf (0))),
  (.branch 15 (.leaf (-10)) (.branch 20 (.leaf (-8)) (.leaf (-5)))),
  (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.leaf (-4)) (.branch 20 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-1))]
def witnessD6_013_397 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 6 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4))))) (.branch 16 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (5))))))
  code := certificateD6_397
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (5)) (.leaf (6))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (7)) (.leaf (8))) (.branch 13 (.leaf (9)) (.leaf (10)))) (.branch 18 (.branch 16 (.leaf (11)) (.leaf (12))) (.branch 19 (.leaf (13)) (.leaf (14)))))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 3 (.leaf (-6)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 14 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_013_398 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (4)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (1)))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (5)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (2)))))))
  code := certificateD6_398
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 11 (.leaf (5)) (.branch 12 (.leaf (6)) (.leaf (7)))) (.branch 16 (.leaf (8)) (.branch 18 (.leaf (9)) (.leaf (10)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_013_399 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_399
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-8)) (.leaf (-9)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 11 (.branch 3 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-9)))),
  (.leaf (-1)),
  (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 17 (.branch 15 (.leaf (-8)) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 18 (.leaf (-5)) (.branch 19 (.leaf (-4)) (.leaf (-3))))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_013_400 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (5))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (1)))))))
  code := certificateD6_400
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 15 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 17 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 16 (.leaf (-11)) (.branch 19 (.leaf (-10)) (.leaf (-7)))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 9 (.branch 7 (.leaf (-14)) (.branch 8 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_013_401 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (5))) (.branch 9 (.leaf (0)) (.leaf (1))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (1))))))
  code := certificateD6_401
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 14 (.branch 11 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))) (.branch 17 (.branch 16 (.leaf (9)) (.leaf (10))) (.branch 19 (.leaf (11)) (.leaf (12)))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 18 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-17)) (.leaf (-16))) (.branch 6 (.leaf (-15)) (.leaf (-14)))) (.branch 9 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 10 (.leaf (-11)) (.leaf (-10))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-9)) (.leaf (-8))) (.branch 14 (.leaf (-7)) (.leaf (-6)))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-12)) (.branch 10 (.leaf (-11)) (.leaf (-10)))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_013_402 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (0)))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (0))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_402
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 15 (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))) (.branch 17 (.leaf (9)) (.branch 19 (.leaf (10)) (.leaf (11)))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 16 (.branch 3 (.leaf (-10)) (.leaf (-9))) (.branch 18 (.leaf (-8)) (.leaf (-7)))),
  (.branch 12 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_013_403 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (5)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (3)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (1)))))))
  code := certificateD6_403
  counts := ![(.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 11 (.leaf (5)) (.branch 13 (.leaf (6)) (.leaf (7)))) (.branch 17 (.leaf (8)) (.branch 18 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.leaf (-2)) (.branch 14 (.leaf (-1)) (.leaf (0)))),
  (.branch 17 (.branch 6 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 4 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_013_404 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (0))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_404
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 11 (.leaf (5)) (.branch 13 (.leaf (6)) (.leaf (7)))) (.branch 17 (.leaf (8)) (.branch 19 (.leaf (9)) (.leaf (10)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 14 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 15 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-4)))),
  (.branch 13 (.branch 9 (.branch 7 (.leaf (-14)) (.branch 8 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_013_405 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (4)))))))
  code := certificateD6_405
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 19 (.leaf (-4)) (.leaf (-2))),
  (.leaf (-2)),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_013_406 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (3)) (.branch 19 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_406
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 11 (.leaf (5)) (.branch 13 (.leaf (6)) (.leaf (7)))) (.branch 17 (.leaf (8)) (.branch 19 (.leaf (9)) (.leaf (10)))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_013_407 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_407
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-6)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 10 (.branch 4 (.leaf (-19)) (.branch 7 (.leaf (-18)) (.leaf (-17)))) (.branch 16 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-7))))),
  (.branch 14 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7)))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_013_408 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (5)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (2)))))))
  code := certificateD6_408
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 10 (.branch 4 (.leaf (-19)) (.branch 7 (.leaf (-18)) (.leaf (-17)))) (.branch 16 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-7))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.leaf (-1)) (.leaf (0))),
  (.branch 12 (.leaf (-3)) (.leaf (-2))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-13)) (.branch 9 (.leaf (-12)) (.leaf (-11)))) (.branch 11 (.leaf (-10)) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_013_409 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (5)) (.leaf (0))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (3)) (.leaf (2)))))))
  code := certificateD6_409
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 13 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 18 (.branch 14 (.leaf (-9)) (.leaf (-8))) (.branch 19 (.leaf (-6)) (.leaf (-4)))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 6 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-3)))),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-12)) (.branch 10 (.leaf (-11)) (.leaf (-10)))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_013_410 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_410
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-6)) (.leaf (-9)))),
  (.leaf (0))]
  high := ![(.branch 10 (.branch 4 (.leaf (-19)) (.branch 7 (.leaf (-18)) (.leaf (-17)))) (.branch 16 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-7))))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.leaf (-2)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7)))) (.branch 18 (.branch 17 (.leaf (-6)) (.leaf (-5))) (.branch 19 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (0))]
def witnessD6_013_411 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_411
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 16 (.leaf (7)) (.branch 18 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-13)))) (.branch 7 (.leaf (-15)) (.branch 18 (.leaf (-17)) (.leaf (-18))))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 19 (.leaf (-18)) (.leaf (-9))),
  (.branch 7 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 18 (.branch 5 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-12)) (.branch 10 (.leaf (-11)) (.leaf (-10)))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_013_412 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (3)) (.branch 19 (.leaf (5)) (.leaf (2)))))))
  code := certificateD6_412
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 18 (.leaf (-4)) (.branch 19 (.leaf (-3)) (.leaf (-2)))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 11 (.leaf (-4)) (.branch 19 (.leaf (-3)) (.leaf (-2)))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD6_013_413 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (2)))))))
  code := certificateD6_413
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 19 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 10 (.branch 4 (.leaf (-19)) (.branch 7 (.leaf (-18)) (.leaf (-17)))) (.branch 16 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-7))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (-3)),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_013_414 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_414
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 19 (.leaf (-4)) (.leaf (-2))),
  (.branch 16 (.leaf (-5)) (.leaf (-3))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_013_415 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (5)))))))
  code := certificateD6_415
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-13)))),
  (.leaf (0))]
  high := ![(.branch 10 (.branch 4 (.leaf (-19)) (.branch 7 (.leaf (-18)) (.leaf (-17)))) (.branch 16 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-7))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-13)) (.leaf (-12))) (.branch 14 (.leaf (-11)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))))),
  (.leaf (0))]
def witnessD6_013_416 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (5)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (4))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_416
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 19 (.leaf (-4)) (.leaf (-2))),
  (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-12))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 6 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_013_417 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (4)))))))
  code := certificateD6_417
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 8 (.leaf (-5)) (.branch 11 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 8 (.branch 2 (.leaf (-13)) (.branch 5 (.leaf (-12)) (.leaf (-11)))) (.branch 14 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.leaf (-7))))),
  (.branch 12 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_013_418 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (0))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (4)) (.leaf (3)))))))
  code := certificateD6_418
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 19 (.leaf (-6)) (.leaf (-3))),
  (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-9))) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 7 (.leaf (-2)) (.branch 14 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_013_419 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (0))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (5)) (.leaf (0))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_419
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.leaf (-5)) (.leaf (-3))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 13 (.branch 9 (.branch 7 (.leaf (-14)) (.branch 8 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_013 : Fin 48 → CycleWitness 6 := ![witnessD6_013_372, witnessD6_013_373, witnessD6_013_374, witnessD6_013_375, witnessD6_013_376, witnessD6_013_377, witnessD6_013_378, witnessD6_013_379, witnessD6_013_380, witnessD6_013_381, witnessD6_013_382, witnessD6_013_383, witnessD6_013_384, witnessD6_013_385, witnessD6_013_386, witnessD6_013_387, witnessD6_013_388, witnessD6_013_389, witnessD6_013_390, witnessD6_013_391, witnessD6_013_392, witnessD6_013_393, witnessD6_013_394, witnessD6_013_395, witnessD6_013_396, witnessD6_013_397, witnessD6_013_398, witnessD6_013_399, witnessD6_013_400, witnessD6_013_401, witnessD6_013_402, witnessD6_013_403, witnessD6_013_404, witnessD6_013_405, witnessD6_013_406, witnessD6_013_407, witnessD6_013_408, witnessD6_013_409, witnessD6_013_410, witnessD6_013_411, witnessD6_013_412, witnessD6_013_413, witnessD6_013_414, witnessD6_013_415, witnessD6_013_416, witnessD6_013_417, witnessD6_013_418, witnessD6_013_419]
end RealPinwheel.FiveSixths


