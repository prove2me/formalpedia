-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_161
-- name    : RealPinwheel_FiveSixths_WitnessD8_161
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:17:12.950311+00:00
-- url     : https://prove2.me/theorems/71af5e63-72fd-4143-a671-1cd26c7a623c
-- title:
--   Exact witness block D8_161
-- statement:
--   These exact witnesses represent words 1481 through 1497 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1481–1497; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_161_1480 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (6)) (.leaf (2))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (3))) (.branch 14 (.leaf (1)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (7)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (2))) (.branch 29 (.leaf (6)) (.leaf (1))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (3))) (.branch 36 (.leaf (0)) (.leaf (5))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (7)) (.leaf (2))) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (3))) (.branch 44 (.leaf (1)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (6)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (1))) (.branch 55 (.leaf (4)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (2))) (.branch 59 (.leaf (7)) (.leaf (1))))))))
  code := certificateD8_1480
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 14 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 32 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 32 (.leaf (-13)) (.leaf (-18)))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (-8))) (.branch 49 (.leaf (-12)) (.leaf (-14)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 47 (.leaf (-7)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.leaf (-1)) (.leaf (0))),
  (.branch 46 (.branch 33 (.leaf (-18)) (.leaf (-17))) (.branch 59 (.leaf (-16)) (.leaf (-13)))),
  (.branch 58 (.branch 50 (.leaf (-14)) (.leaf (-13))) (.branch 59 (.leaf (-10)) (.leaf (-7)))),
  (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5))))),
  (.branch 56 (.branch 54 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_161_1481 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (1))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (1)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (7)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (5)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (6))) (.branch 29 (.leaf (1)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (3))) (.branch 36 (.leaf (0)) (.leaf (7))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (1))) (.branch 40 (.leaf (5)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (1)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (6)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (4))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (1))) (.branch 55 (.leaf (5)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (7))) (.branch 59 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_1481
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 18 (.leaf (0)) (.branch 37 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 58 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 54 (.leaf (-1)) (.leaf (0))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 50 (.branch 8 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_161_1482 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (7)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (6))) (.branch 21 (.leaf (0)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (7))) (.branch 29 (.leaf (1)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (6)))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (5))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (3)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (7)) (.leaf (4))) (.branch 44 (.leaf (6)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (5))) (.branch 51 (.leaf (0)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (2))) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (6)) (.leaf (7))) (.branch 59 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_1482
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 15 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 24 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 54 (.leaf (-20)) (.leaf (-22)))),
  (.branch 22 (.leaf (0)) (.branch 52 (.leaf (-2)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-6)) (.leaf (-7)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-19))) (.branch 37 (.leaf (-22)) (.leaf (-26)))),
  (.branch 7 (.leaf (0)) (.branch 44 (.leaf (-11)) (.leaf (-12)))),
  (.branch 12 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 57 (.branch 55 (.leaf (-22)) (.branch 56 (.leaf (-19)) (.leaf (-16)))) (.branch 58 (.leaf (-13)) (.branch 59 (.leaf (-10)) (.leaf (-7))))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.branch 56 (.leaf (-1)) (.leaf (0))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 38 (.leaf (-26)) (.leaf (-25))) (.branch 52 (.leaf (-23)) (.branch 53 (.leaf (-21)) (.leaf (-19))))) (.branch 57 (.branch 55 (.leaf (-17)) (.branch 56 (.leaf (-15)) (.leaf (-13)))) (.branch 58 (.leaf (-11)) (.branch 59 (.leaf (-9)) (.leaf (-7)))))),
  (.branch 58 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 59 (.leaf (-9)) (.leaf (-7)))),
  (.branch 43 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_161_1483 : CycleWitness 8 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (6)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (5))) (.branch 20 (.leaf (7)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (1))) (.branch 24 (.leaf (4)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (3))) (.branch 28 (.leaf (2)) (.leaf (0))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (6)) (.branch 31 (.leaf (1)) (.leaf (5)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (4))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (3)) (.leaf (7)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (2))) (.branch 43 (.leaf (1)) (.leaf (5)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (4)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (2)) (.leaf (0))) (.branch 50 (.leaf (6)) (.leaf (3))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (1)) (.leaf (0))) (.branch 54 (.leaf (5)) (.leaf (2)))) (.branch 57 (.branch 56 (.leaf (1)) (.leaf (0))) (.branch 58 (.leaf (4)) (.leaf (7))))))))
  code := certificateD8_1483
  counts := ![(.branch 29 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.leaf (15)))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 38 (.leaf (9)) (.leaf (10)))) (.branch 52 (.branch 47 (.leaf (11)) (.leaf (12))) (.branch 56 (.leaf (13)) (.leaf (14)))))),
  (.branch 28 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-44))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 14 (.leaf (-20)) (.leaf (-26)))) (.branch 34 (.branch 26 (.leaf (-29)) (.leaf (-35))) (.branch 38 (.leaf (-41)) (.leaf (-44))))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-29)) (.leaf (-42)))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-39)) (.leaf (-42)))),
  (.branch 46 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.branch 54 (.leaf (-5)) (.leaf (-6)))),
  (.branch 10 (.leaf (0)) (.leaf (-29))),
  (.leaf (0))]
  high := ![(.branch 30 (.branch 14 (.branch 6 (.branch 2 (.leaf (-44)) (.leaf (-43))) (.branch 10 (.leaf (-42)) (.leaf (-41)))) (.branch 22 (.branch 18 (.leaf (-40)) (.leaf (-39))) (.branch 26 (.leaf (-38)) (.leaf (-37))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (-36)) (.leaf (-35))) (.branch 42 (.leaf (-34)) (.leaf (-33)))) (.branch 54 (.branch 50 (.leaf (-32)) (.leaf (-31))) (.branch 58 (.leaf (-30)) (.leaf (-15)))))),
  (.branch 48 (.branch 39 (.leaf (-44)) (.leaf (-43))) (.branch 57 (.leaf (-42)) (.branch 58 (.leaf (-35)) (.leaf (-28))))),
  (.branch 49 (.branch 9 (.leaf (-42)) (.branch 29 (.leaf (-41)) (.leaf (-40)))) (.branch 57 (.branch 56 (.leaf (-37)) (.leaf (-29))) (.branch 58 (.leaf (-21)) (.leaf (-13))))),
  (.branch 54 (.branch 40 (.branch 28 (.leaf (-42)) (.leaf (-41))) (.branch 52 (.leaf (-40)) (.branch 53 (.leaf (-35)) (.leaf (-30))))) (.branch 56 (.branch 55 (.leaf (-25)) (.leaf (-20))) (.branch 57 (.leaf (-15)) (.branch 58 (.leaf (-10)) (.leaf (-5)))))),
  (.leaf (-2)),
  (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2))))),
  (.branch 53 (.branch 31 (.branch 11 (.leaf (-29)) (.leaf (-28))) (.branch 51 (.leaf (-27)) (.branch 52 (.leaf (-24)) (.leaf (-21))))) (.branch 56 (.branch 54 (.leaf (-18)) (.branch 55 (.leaf (-15)) (.leaf (-12)))) (.branch 57 (.leaf (-9)) (.branch 58 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (0))]
def witnessD8_161_1484 : CycleWitness 8 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (7))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (6)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (3))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (7)) (.leaf (2))) (.branch 24 (.leaf (6)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (3))) (.branch 28 (.leaf (4)) (.leaf (2))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (5)) (.branch 31 (.leaf (0)) (.leaf (1)))) (.branch 34 (.branch 33 (.leaf (3)) (.leaf (6))) (.branch 35 (.leaf (0)) (.leaf (2))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (7)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (3)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (5))) (.branch 43 (.leaf (2)) (.leaf (1)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (6)) (.leaf (4)))) (.branch 49 (.branch 48 (.leaf (3)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (0))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (7)) (.leaf (5))) (.branch 54 (.leaf (0)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (3)) (.leaf (2))) (.branch 58 (.leaf (4)) (.leaf (6))))))))
  code := certificateD8_1484
  counts := ![(.branch 25 (.branch 11 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 50 (.leaf (7)) (.branch 57 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 10 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 13 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 54 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 49 (.leaf (-39)) (.leaf (-41)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-15))) (.branch 29 (.leaf (-18)) (.leaf (-19)))),
  (.branch 33 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 40 (.leaf (-9)) (.leaf (-10)))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (-1))) (.branch 47 (.leaf (-8)) (.leaf (-11)))),
  (.branch 6 (.leaf (0)) (.branch 53 (.leaf (-29)) (.leaf (-30)))),
  (.branch 34 (.branch 24 (.leaf (0)) (.leaf (-2))) (.branch 46 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-31)))]
  high := ![(.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2))))),
  (.branch 56 (.branch 50 (.leaf (-41)) (.leaf (-40))) (.branch 57 (.leaf (-30)) (.branch 58 (.leaf (-20)) (.leaf (-10))))),
  (.branch 44 (.branch 30 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17)))) (.branch 51 (.leaf (-16)) (.branch 58 (.leaf (-15)) (.leaf (-11))))),
  (.branch 49 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-6)) (.leaf (-4))))),
  (.branch 48 (.leaf (-11)) (.leaf (-10))),
  (.branch 56 (.branch 54 (.leaf (-30)) (.branch 55 (.leaf (-25)) (.leaf (-20)))) (.branch 57 (.leaf (-15)) (.branch 58 (.leaf (-10)) (.leaf (-5))))),
  (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-6))) (.branch 49 (.leaf (-4)) (.branch 50 (.leaf (-2)) (.leaf (0))))),
  (.branch 54 (.branch 23 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 38 (.leaf (-29)) (.branch 53 (.leaf (-28)) (.leaf (-24))))) (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-16))) (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-8)) (.leaf (-4))))))]
def witnessD8_161_1485 : CycleWitness 8 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (7)) (.leaf (4))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (5))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (1))) (.branch 24 (.leaf (4)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (7)) (.leaf (2))) (.branch 28 (.leaf (1)) (.leaf (3))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (5)) (.leaf (1)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (6))) (.branch 35 (.leaf (0)) (.leaf (4))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (3)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (0)))) (.branch 42 (.branch 41 (.leaf (7)) (.leaf (5))) (.branch 43 (.leaf (1)) (.leaf (2)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (3)) (.branch 46 (.leaf (0)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (4)) (.leaf (6))) (.branch 50 (.leaf (2)) (.leaf (0))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (1)) (.leaf (5))) (.branch 54 (.leaf (3)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (2)) (.leaf (7))) (.branch 58 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_1485
  counts := ![(.branch 25 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 33 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 36 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-4)) (.leaf (-5)))),
  (.branch 32 (.branch 2 (.leaf (0)) (.branch 17 (.leaf (-7)) (.leaf (-10)))) (.branch 47 (.leaf (-13)) (.branch 52 (.leaf (-16)) (.leaf (-17))))),
  (.branch 3 (.leaf (0)) (.branch 44 (.leaf (-29)) (.leaf (-32)))),
  (.branch 29 (.branch 4 (.leaf (0)) (.leaf (-19))) (.branch 37 (.leaf (-24)) (.branch 45 (.leaf (-27)) (.leaf (-30))))),
  (.leaf (0)),
  (.branch 42 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 53 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-10)) (.leaf (-12)))),
  (.branch 11 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.leaf (-2)))),
  (.branch 53 (.leaf (-17)) (.leaf (-16))),
  (.branch 51 (.branch 45 (.leaf (-32)) (.leaf (-31))) (.branch 57 (.leaf (-30)) (.branch 58 (.leaf (-20)) (.leaf (-10))))),
  (.branch 56 (.branch 46 (.leaf (-30)) (.branch 55 (.leaf (-29)) (.leaf (-25)))) (.branch 57 (.leaf (-21)) (.branch 58 (.leaf (-17)) (.leaf (-13))))),
  (.leaf (0)),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2))))),
  (.branch 53 (.branch 50 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 42 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2))))]
def witnessD8_161_1486 : CycleWitness 8 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (7)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (3))) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (4))) (.branch 24 (.leaf (6)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (5)) (.leaf (0))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (3)) (.branch 31 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (7))) (.branch 35 (.leaf (4)) (.leaf (1))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (3)) (.leaf (5)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (6)) (.leaf (2)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (4)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (3))) (.branch 50 (.leaf (2)) (.leaf (1))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (7))) (.branch 54 (.leaf (5)) (.leaf (2)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (3)) (.leaf (4))))))))
  code := certificateD8_1486
  counts := ![(.branch 29 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.leaf (15)))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 48 (.leaf (-44)) (.leaf (-47)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 55 (.leaf (-4)) (.leaf (-5)))),
  (.branch 19 (.leaf (0)) (.branch 58 (.leaf (-1)) (.leaf (-2)))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (-7))) (.branch 28 (.leaf (-8)) (.branch 40 (.leaf (-11)) (.leaf (-12))))),
  (.branch 4 (.leaf (0)) (.branch 43 (.leaf (-47)) (.leaf (-48)))),
  (.branch 14 (.leaf (0)) (.branch 53 (.leaf (-17)) (.leaf (-18))))]
  high := ![(.branch 53 (.branch 49 (.leaf (-47)) (.leaf (-46))) (.branch 57 (.leaf (-45)) (.branch 58 (.leaf (-30)) (.leaf (-15))))),
  (.branch 52 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2)))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 24 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 36 (.leaf (-2)) (.branch 48 (.leaf (-1)) (.leaf (0))))),
  (.branch 56 (.branch 41 (.leaf (-12)) (.branch 55 (.leaf (-11)) (.leaf (-10)))) (.branch 57 (.leaf (-9)) (.branch 58 (.leaf (-8)) (.leaf (-7))))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-48)) (.leaf (-45))) (.branch 46 (.leaf (-42)) (.leaf (-39)))) (.branch 49 (.branch 48 (.leaf (-36)) (.leaf (-33))) (.branch 50 (.leaf (-30)) (.leaf (-27))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-24)) (.leaf (-21))) (.branch 54 (.leaf (-18)) (.leaf (-15)))) (.branch 57 (.branch 56 (.leaf (-12)) (.leaf (-9))) (.branch 58 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 56 (.branch 54 (.leaf (-18)) (.branch 55 (.leaf (-15)) (.leaf (-12)))) (.branch 57 (.leaf (-9)) (.branch 58 (.leaf (-6)) (.leaf (-3)))))]
def witnessD8_161_1487 : CycleWitness 8 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (6)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (7)) (.branch 16 (.leaf (0)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (2))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (6))) (.branch 24 (.leaf (1)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (2))) (.branch 28 (.leaf (0)) (.leaf (5))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (7)) (.branch 31 (.leaf (0)) (.leaf (1)))) (.branch 34 (.branch 33 (.leaf (4)) (.leaf (0))) (.branch 35 (.leaf (6)) (.leaf (2))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (1)) (.leaf (0)))) (.branch 42 (.branch 41 (.leaf (5)) (.leaf (7))) (.branch 43 (.leaf (0)) (.leaf (4)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (2)) (.branch 46 (.leaf (0)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (6)) (.leaf (0))) (.branch 50 (.leaf (3)) (.leaf (0))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (5)) (.leaf (1))) (.branch 54 (.leaf (0)) (.leaf (2)))) (.branch 57 (.branch 56 (.leaf (4)) (.leaf (0))) (.branch 58 (.leaf (7)) (.leaf (6))))))))
  code := certificateD8_1487
  counts := ![(.branch 28 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 40 (.leaf (13)) (.leaf (14))))) (.branch 51 (.branch 46 (.leaf (15)) (.branch 49 (.leaf (16)) (.leaf (17)))) (.branch 54 (.leaf (18)) (.branch 57 (.leaf (19)) (.leaf (20))))))),
  (.branch 24 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.leaf (7))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 51 (.leaf (-39)) (.leaf (-42)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-38))) (.branch 53 (.leaf (-41)) (.leaf (-45)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 27 (.leaf (-6)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-44)) (.leaf (-48)))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 29 (.branch 6 (.leaf (0)) (.leaf (-6))) (.branch 52 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (-1))) (.branch 42 (.leaf (-2)) (.leaf (-9))))]
  high := ![(.branch 55 (.branch 52 (.leaf (-42)) (.leaf (-41))) (.branch 58 (.leaf (-40)) (.leaf (-20)))),
  (.branch 56 (.branch 54 (.leaf (-45)) (.branch 55 (.leaf (-38)) (.leaf (-31)))) (.branch 57 (.leaf (-24)) (.branch 58 (.leaf (-17)) (.leaf (-10))))),
  (.branch 56 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.branch 58 (.leaf (-6)) (.leaf (-5))))),
  (.branch 53 (.branch 39 (.branch 15 (.leaf (-48)) (.branch 27 (.leaf (-47)) (.leaf (-46)))) (.branch 51 (.leaf (-45)) (.branch 52 (.leaf (-40)) (.leaf (-35))))) (.branch 56 (.branch 54 (.leaf (-30)) (.branch 55 (.leaf (-25)) (.leaf (-20)))) (.branch 57 (.leaf (-15)) (.branch 58 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2)))),
  (.branch 55 (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.leaf (-2))))),
  (.branch 36 (.leaf (-1)) (.leaf (0))),
  (.branch 43 (.leaf (-9)) (.leaf (-8)))]
def witnessD8_161_1488 : CycleWitness 8 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (2))) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (7)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (1))) (.branch 20 (.leaf (5)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (4))) (.branch 24 (.leaf (6)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (5))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (4)))) (.branch 34 (.branch 33 (.leaf (3)) (.leaf (7))) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (1)) (.leaf (5))) (.branch 39 (.leaf (3)) (.leaf (2)))) (.branch 42 (.branch 41 (.leaf (4)) (.leaf (0))) (.branch 43 (.leaf (1)) (.leaf (6)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (3)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (5)) (.leaf (1))) (.branch 50 (.leaf (4)) (.leaf (0))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (2)) (.leaf (7))) (.branch 54 (.leaf (3)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_1488
  counts := ![(.branch 27 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 30 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 35 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.leaf (7))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 21 (.branch 1 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-12)))) (.branch 30 (.leaf (-13)) (.branch 45 (.leaf (-17)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-39)) (.leaf (-47)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-23))) (.branch 39 (.leaf (-26)) (.branch 46 (.leaf (-33)) (.leaf (-36))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (-8))) (.branch 57 (.leaf (-9)) (.leaf (-11)))),
  (.branch 9 (.leaf (0)) (.branch 38 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-47))),
  (.branch 14 (.leaf (0)) (.branch 53 (.leaf (-17)) (.leaf (-18))))]
  high := ![(.branch 57 (.leaf (-20)) (.branch 58 (.leaf (-18)) (.leaf (-16)))),
  (.branch 38 (.branch 20 (.branch 14 (.leaf (-47)) (.leaf (-46))) (.branch 26 (.leaf (-45)) (.branch 32 (.leaf (-44)) (.leaf (-43))))) (.branch 56 (.branch 44 (.leaf (-42)) (.branch 50 (.leaf (-41)) (.leaf (-40)))) (.branch 57 (.leaf (-30)) (.branch 58 (.leaf (-20)) (.leaf (-10)))))),
  (.branch 53 (.leaf (-2)) (.branch 54 (.leaf (-1)) (.leaf (0)))),
  (.branch 56 (.branch 47 (.leaf (-36)) (.branch 55 (.leaf (-34)) (.leaf (-29)))) (.branch 57 (.leaf (-24)) (.branch 58 (.leaf (-19)) (.leaf (-14))))),
  (.branch 58 (.leaf (-11)) (.leaf (-8))),
  (.leaf (-2)),
  (.branch 50 (.branch 46 (.branch 25 (.branch 5 (.leaf (-47)) (.leaf (-46))) (.branch 45 (.leaf (-45)) (.leaf (-42)))) (.branch 48 (.branch 47 (.leaf (-39)) (.leaf (-36))) (.branch 49 (.leaf (-33)) (.leaf (-30))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-27)) (.leaf (-24))) (.branch 53 (.leaf (-21)) (.leaf (-18)))) (.branch 56 (.branch 55 (.leaf (-15)) (.leaf (-12))) (.branch 57 (.leaf (-9)) (.branch 58 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 56 (.branch 54 (.leaf (-18)) (.branch 55 (.leaf (-15)) (.leaf (-12)))) (.branch 57 (.leaf (-9)) (.branch 58 (.leaf (-6)) (.leaf (-3)))))]
def witnessD8_161_1489 : CycleWitness 8 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (4))) (.branch 6 (.leaf (6)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (7)) (.branch 9 (.leaf (2)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (5))) (.branch 13 (.leaf (0)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (6)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (4))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (5))) (.branch 24 (.leaf (7)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (2))) (.branch 28 (.leaf (1)) (.leaf (6))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (4)) (.branch 31 (.leaf (0)) (.leaf (2)))) (.branch 34 (.branch 33 (.leaf (3)) (.leaf (1))) (.branch 35 (.leaf (5)) (.leaf (4))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (7)) (.leaf (1)))) (.branch 42 (.branch 41 (.leaf (3)) (.leaf (6))) (.branch 43 (.leaf (0)) (.leaf (2)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (4)) (.branch 46 (.leaf (1)) (.leaf (5)))) (.branch 49 (.branch 48 (.leaf (3)) (.leaf (0))) (.branch 50 (.leaf (2)) (.leaf (7))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (1)) (.leaf (6))) (.branch 54 (.leaf (4)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (3)) (.leaf (2))) (.branch 58 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_1489
  counts := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 12 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-49))),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-31))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 36 (.leaf (-6)) (.leaf (-9)))),
  (.branch 23 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.branch 51 (.leaf (-15)) (.leaf (-22))))]
  high := ![(.branch 32 (.branch 14 (.branch 2 (.leaf (-49)) (.branch 8 (.leaf (-48)) (.leaf (-47)))) (.branch 20 (.leaf (-46)) (.branch 26 (.leaf (-45)) (.leaf (-44))))) (.branch 50 (.branch 38 (.leaf (-43)) (.branch 44 (.leaf (-42)) (.leaf (-41)))) (.branch 57 (.branch 56 (.leaf (-40)) (.leaf (-30))) (.branch 58 (.leaf (-20)) (.leaf (-10)))))),
  (.branch 29 (.branch 11 (.branch 5 (.leaf (-19)) (.leaf (-18))) (.branch 17 (.leaf (-17)) (.branch 23 (.leaf (-16)) (.leaf (-15))))) (.branch 41 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 47 (.leaf (-12)) (.branch 53 (.leaf (-11)) (.leaf (-10)))))),
  (.branch 51 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2)))),
  (.branch 34 (.branch 4 (.leaf (-31)) (.branch 19 (.leaf (-30)) (.leaf (-29)))) (.branch 57 (.branch 49 (.leaf (-28)) (.leaf (-24))) (.branch 58 (.leaf (-17)) (.leaf (-10))))),
  (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.branch 58 (.leaf (-6)) (.leaf (-5))))),
  (.branch 36 (.branch 24 (.leaf (-3)) (.leaf (-2))) (.branch 48 (.leaf (-1)) (.leaf (0)))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2))))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-22)) (.leaf (-20))) (.branch 54 (.leaf (-18)) (.leaf (-16)))) (.branch 57 (.branch 56 (.leaf (-14)) (.leaf (-12))) (.branch 58 (.leaf (-10)) (.leaf (-8)))))]
def witnessD8_161_1490 : CycleWitness 8 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (7))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (4)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (6)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (3))) (.branch 20 (.leaf (5)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (4))) (.branch 24 (.leaf (1)) (.leaf (7)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (2)) (.leaf (1))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (5)) (.branch 31 (.leaf (0)) (.leaf (4)))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (2))) (.branch 35 (.leaf (3)) (.leaf (0))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (6)) (.leaf (1))) (.branch 39 (.leaf (5)) (.leaf (0)))) (.branch 42 (.branch 41 (.leaf (2)) (.leaf (4))) (.branch 43 (.leaf (3)) (.leaf (1)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (7)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (5))) (.branch 50 (.leaf (0)) (.leaf (3))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (4)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (6)) (.leaf (3))) (.branch 58 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_1490
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 40 (.leaf (-47)) (.leaf (-51)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-23))) (.branch 34 (.leaf (-26)) (.branch 47 (.leaf (-28)) (.leaf (-29))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-11))) (.branch 19 (.leaf (-14)) (.branch 57 (.leaf (-17)) (.leaf (-20))))),
  (.branch 3 (.leaf (0)) (.branch 32 (.leaf (-41)) (.leaf (-44)))),
  (.branch 39 (.leaf (0)) (.leaf (-2))),
  (.branch 17 (.leaf (0)) (.branch 56 (.leaf (-8)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (-13)) (.leaf (-15))))]
  high := ![(.branch 51 (.branch 41 (.leaf (-51)) (.branch 46 (.leaf (-50)) (.leaf (-49)))) (.branch 57 (.branch 56 (.leaf (-48)) (.leaf (-36))) (.branch 58 (.leaf (-24)) (.leaf (-12))))),
  (.leaf (-2)),
  (.branch 56 (.branch 48 (.leaf (-29)) (.branch 55 (.leaf (-27)) (.leaf (-22)))) (.branch 57 (.leaf (-17)) (.branch 58 (.leaf (-12)) (.leaf (-7))))),
  (.branch 58 (.leaf (-20)) (.leaf (-16))),
  (.branch 54 (.branch 43 (.branch 33 (.leaf (-44)) (.leaf (-43))) (.branch 53 (.leaf (-42)) (.leaf (-36)))) (.branch 56 (.branch 55 (.leaf (-30)) (.leaf (-24))) (.branch 57 (.leaf (-18)) (.branch 58 (.leaf (-12)) (.leaf (-6)))))),
  (.branch 40 (.leaf (-2)) (.branch 50 (.leaf (-1)) (.leaf (0)))),
  (.branch 57 (.leaf (-9)) (.branch 58 (.leaf (-6)) (.leaf (-3)))),
  (.branch 52 (.branch 48 (.branch 26 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 55 (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.leaf (-2))))))]
def witnessD8_161_1491 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (2)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (6))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (1))))))) (.branch 44 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (5)) (.leaf (0))))) (.branch 40 (.branch 38 (.leaf (2)) (.branch 39 (.leaf (1)) (.leaf (0)))) (.branch 42 (.branch 41 (.leaf (4)) (.leaf (0))) (.branch 43 (.leaf (1)) (.leaf (3)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (7))) (.branch 50 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.leaf (3)) (.branch 53 (.leaf (0)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (4)) (.leaf (0))) (.branch 57 (.leaf (2)) (.leaf (1))))))))
  code := certificateD8_1491
  counts := ![(.branch 27 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 13 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))) (.branch 42 (.branch 34 (.branch 30 (.leaf (11)) (.branch 31 (.leaf (12)) (.leaf (13)))) (.branch 37 (.leaf (14)) (.branch 40 (.leaf (15)) (.leaf (16))))) (.branch 51 (.branch 45 (.leaf (17)) (.branch 48 (.leaf (18)) (.leaf (19)))) (.branch 53 (.leaf (20)) (.branch 56 (.leaf (21)) (.leaf (22))))))),
  (.branch 29 (.branch 14 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 31 (.leaf (-24)) (.leaf (-30)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 35 (.leaf (-4)) (.leaf (-5)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-2)) (.leaf (-4)))),
  (.branch 23 (.branch 4 (.leaf (0)) (.leaf (-6))) (.branch 52 (.leaf (-7)) (.leaf (-8)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-22))),
  (.branch 20 (.leaf (0)) (.leaf (-38))),
  (.branch 49 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 43 (.branch 32 (.leaf (-30)) (.leaf (-29))) (.branch 54 (.leaf (-28)) (.branch 57 (.leaf (-26)) (.leaf (-19))))),
  (.branch 51 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.leaf (0)))),
  (.branch 48 (.leaf (-4)) (.leaf (-3))),
  (.branch 55 (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3))))),
  (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))),
  (.branch 47 (.branch 41 (.branch 38 (.branch 37 (.leaf (-22)) (.leaf (-21))) (.branch 39 (.leaf (-20)) (.branch 40 (.leaf (-19)) (.leaf (-18))))) (.branch 44 (.branch 42 (.leaf (-17)) (.branch 43 (.leaf (-16)) (.leaf (-15)))) (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-13)) (.leaf (-12)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-10))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (-38)) (.leaf (-37))) (.branch 23 (.leaf (-36)) (.leaf (-35)))) (.branch 26 (.branch 25 (.leaf (-34)) (.leaf (-33))) (.branch 27 (.leaf (-32)) (.branch 28 (.leaf (-31)) (.leaf (-30)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-29)) (.leaf (-28))) (.branch 32 (.leaf (-27)) (.branch 33 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 35 (.leaf (-24)) (.leaf (-23))) (.branch 37 (.leaf (-22)) (.branch 38 (.leaf (-21)) (.leaf (-20))))))) (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (-19)) (.leaf (-18))) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 45 (.branch 44 (.leaf (-15)) (.leaf (-14))) (.branch 46 (.leaf (-13)) (.branch 47 (.leaf (-12)) (.leaf (-11)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-8)) (.branch 52 (.leaf (-7)) (.leaf (-6))))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 53 (.branch 51 (.branch 50 (.leaf (-9)) (.leaf (-8))) (.branch 52 (.leaf (-7)) (.leaf (-6)))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_161_1492 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (4)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (6)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (0)))))) (.branch 22 (.branch 19 (.branch 16 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (5)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (0))))) (.branch 25 (.branch 23 (.leaf (1)) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (7))) (.branch 28 (.leaf (0)) (.leaf (4))))))) (.branch 44 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (5)) (.leaf (0)))) (.branch 42 (.branch 41 (.leaf (6)) (.leaf (0))) (.branch 43 (.leaf (3)) (.leaf (0)))))) (.branch 51 (.branch 48 (.branch 45 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (4)))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (2)) (.leaf (0))))) (.branch 54 (.branch 52 (.leaf (1)) (.branch 53 (.leaf (0)) (.leaf (3)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (7))) (.branch 57 (.leaf (0)) (.leaf (5))))))))
  code := certificateD8_1492
  counts := ![(.branch 28 (.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 18 (.leaf (10)) (.leaf (11)))) (.branch 24 (.branch 22 (.leaf (12)) (.leaf (13))) (.branch 26 (.leaf (14)) (.leaf (15)))))) (.branch 42 (.branch 35 (.branch 31 (.branch 30 (.leaf (16)) (.leaf (17))) (.branch 33 (.leaf (18)) (.leaf (19)))) (.branch 38 (.branch 36 (.leaf (20)) (.leaf (21))) (.branch 40 (.leaf (22)) (.leaf (23))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (24)) (.leaf (25))) (.branch 47 (.leaf (26)) (.leaf (27)))) (.branch 53 (.branch 51 (.leaf (28)) (.leaf (29))) (.branch 55 (.leaf (30)) (.branch 57 (.leaf (31)) (.leaf (32)))))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.branch 56 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-10)) (.branch 36 (.leaf (-13)) (.leaf (-15))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (-11))) (.branch 52 (.leaf (-17)) (.leaf (-22)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 25 (.leaf (-10)) (.leaf (-11)))),
  (.branch 43 (.branch 8 (.leaf (0)) (.leaf (-4))) (.branch 54 (.leaf (-5)) (.leaf (-6)))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (-28))) (.branch 48 (.leaf (-29)) (.leaf (-30)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-17))),
  (.branch 27 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 52 (.branch 48 (.leaf (-15)) (.branch 50 (.leaf (-14)) (.leaf (-13)))) (.branch 54 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10))))),
  (.branch 55 (.branch 53 (.leaf (-22)) (.branch 54 (.leaf (-20)) (.leaf (-18)))) (.branch 56 (.leaf (-16)) (.branch 57 (.leaf (-14)) (.leaf (-12))))),
  (.branch 53 (.branch 51 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8)))) (.branch 55 (.branch 54 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-30)) (.leaf (-27))) (.branch 51 (.leaf (-24)) (.branch 52 (.leaf (-21)) (.leaf (-18))))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 49 (.branch 45 (.branch 43 (.branch 42 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-15)) (.leaf (-14)))) (.branch 47 (.branch 46 (.leaf (-13)) (.leaf (-12))) (.branch 48 (.leaf (-11)) (.leaf (-10))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-9)) (.leaf (-8))) (.branch 52 (.leaf (-7)) (.leaf (-6)))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_161_1493 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (6)) (.leaf (2))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (5)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (7)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (6)) (.leaf (5))))) (.branch 25 (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (4)) (.leaf (7))))))) (.branch 44 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (5)))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (6)) (.leaf (2))))) (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (1)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (3))) (.branch 43 (.leaf (0)) (.leaf (7)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (5)) (.branch 46 (.leaf (2)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (0))) (.branch 50 (.leaf (6)) (.leaf (4))))) (.branch 54 (.branch 52 (.leaf (3)) (.branch 53 (.leaf (0)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (2))) (.branch 57 (.leaf (5)) (.leaf (7))))))))
  code := certificateD8_1493
  counts := ![(.branch 26 (.branch 12 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 31 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 49 (.branch 43 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 55 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-4)) (.leaf (-5)))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-5)))) (.branch 40 (.leaf (-7)) (.branch 54 (.leaf (-8)) (.leaf (-10))))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-20))),
  (.branch 4 (.leaf (0)) (.leaf (-38))),
  (.branch 10 (.leaf (0)) (.branch 33 (.leaf (-8)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (-15)) (.leaf (-16)))),
  (.leaf (0))]
  high := ![(.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.leaf (-7)))),
  (.branch 47 (.leaf (-7)) (.branch 57 (.leaf (-6)) (.leaf (-3)))),
  (.branch 54 (.branch 43 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3))))),
  (.branch 53 (.branch 40 (.branch 5 (.leaf (-38)) (.leaf (-37))) (.branch 52 (.leaf (-35)) (.leaf (-30)))) (.branch 55 (.branch 54 (.leaf (-25)) (.leaf (-20))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 34 (.leaf (-9)) (.branch 46 (.leaf (-7)) (.leaf (-5)))),
  (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-14))) (.branch 53 (.leaf (-12)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD8_161_1494 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (6)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (5)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (7))) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (5))))) (.branch 25 (.branch 23 (.leaf (6)) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (4)) (.leaf (1))))))) (.branch 44 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (7)) (.leaf (5)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (1)) (.leaf (3))))) (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (2)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (6))) (.branch 43 (.leaf (0)) (.leaf (1)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (5)) (.branch 46 (.leaf (3)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (2)) (.leaf (0))) (.branch 50 (.leaf (1)) (.leaf (4))))) (.branch 54 (.branch 52 (.leaf (7)) (.branch 53 (.leaf (0)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (3))) (.branch 57 (.leaf (5)) (.leaf (1))))))))
  code := certificateD8_1494
  counts := ![(.branch 26 (.branch 12 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 31 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 49 (.branch 43 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 55 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-4)) (.leaf (-5)))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 50 (.leaf (-3)) (.leaf (-4)))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-5)))) (.branch 40 (.leaf (-7)) (.branch 54 (.leaf (-8)) (.leaf (-10))))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-5)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-38))),
  (.branch 10 (.leaf (0)) (.branch 33 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-49))),
  (.branch 13 (.leaf (0)) (.branch 32 (.leaf (-19)) (.leaf (-20))))]
  high := ![(.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 51 (.leaf (-4)) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.leaf (-7)))),
  (.branch 47 (.leaf (-7)) (.branch 57 (.leaf (-6)) (.leaf (-3)))),
  (.branch 53 (.branch 40 (.branch 5 (.leaf (-38)) (.leaf (-37))) (.branch 52 (.leaf (-35)) (.leaf (-30)))) (.branch 55 (.branch 54 (.leaf (-25)) (.leaf (-20))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 34 (.leaf (-9)) (.branch 46 (.leaf (-7)) (.leaf (-5)))),
  (.branch 49 (.branch 45 (.branch 43 (.branch 4 (.leaf (-49)) (.leaf (-48))) (.branch 44 (.leaf (-45)) (.leaf (-42)))) (.branch 47 (.branch 46 (.leaf (-39)) (.leaf (-36))) (.branch 48 (.leaf (-33)) (.leaf (-30))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-27)) (.leaf (-24))) (.branch 52 (.leaf (-21)) (.leaf (-18)))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 54 (.branch 33 (.leaf (-20)) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3)))))]
def witnessD8_161_1495 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (7))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (5)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (1)) (.leaf (4))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (0))) (.branch 35 (.leaf (6)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 41 (.branch 40 (.leaf (5)) (.leaf (0))) (.branch 42 (.leaf (2)) (.leaf (4)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (0)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (3)) (.leaf (0))) (.branch 49 (.leaf (1)) (.leaf (7))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (2)) (.leaf (0))) (.branch 53 (.leaf (5)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (3))) (.branch 57 (.leaf (2)) (.leaf (4))))))))
  code := certificateD8_1495
  counts := ![(.branch 26 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.branch 38 (.leaf (12)) (.leaf (13))))) (.branch 48 (.branch 45 (.leaf (14)) (.leaf (15))) (.branch 52 (.leaf (16)) (.branch 55 (.leaf (17)) (.leaf (18))))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 49 (.leaf (9)) (.branch 54 (.leaf (10)) (.leaf (11)))))),
  (.branch 31 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 51 (.leaf (9)) (.branch 57 (.leaf (10)) (.leaf (11)))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-17)) (.leaf (-27)))) (.branch 32 (.leaf (-37)) (.branch 34 (.leaf (-40)) (.leaf (-50))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 17 (.leaf (-11)) (.branch 22 (.leaf (-13)) (.leaf (-14))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 46 (.leaf (-5)) (.branch 51 (.leaf (-6)) (.leaf (-7))))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-5)) (.leaf (-6)))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (-4))) (.branch 53 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-23))),
  (.branch 21 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 49 (.branch 35 (.leaf (-50)) (.branch 42 (.leaf (-49)) (.leaf (-48)))) (.branch 56 (.leaf (-47)) (.branch 57 (.leaf (-40)) (.leaf (-33))))),
  (.branch 56 (.branch 55 (.leaf (-14)) (.leaf (-11))) (.branch 57 (.leaf (-8)) (.leaf (-5)))),
  (.branch 52 (.leaf (-7)) (.leaf (-5))),
  (.branch 57 (.leaf (-6)) (.leaf (-3))),
  (.branch 44 (.leaf (-1)) (.leaf (0))),
  (.branch 55 (.branch 54 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3))))),
  (.branch 46 (.branch 40 (.branch 37 (.branch 36 (.leaf (-23)) (.leaf (-22))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-20)) (.leaf (-19))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))))) (.branch 52 (.branch 49 (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_161_1496 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (1)) (.leaf (7))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (5)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (1)) (.leaf (6)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (2))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (3)) (.leaf (0))) (.branch 53 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (5))) (.branch 57 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_1496
  counts := ![(.branch 26 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 52 (.leaf (18)) (.branch 55 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 34 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 29 (.leaf (0)) (.branch 58 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-3)) (.branch 52 (.leaf (-4)) (.leaf (-5))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 34 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 25 (.leaf (-11)) (.branch 54 (.leaf (-13)) (.leaf (-14))))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (-34))) (.branch 46 (.leaf (-35)) (.leaf (-36)))),
  (.branch 17 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 50 (.branch 46 (.leaf (-8)) (.leaf (-7))) (.branch 54 (.leaf (-6)) (.leaf (-5)))),
  (.branch 56 (.branch 55 (.leaf (-14)) (.leaf (-11))) (.branch 57 (.leaf (-8)) (.leaf (-5)))),
  (.branch 54 (.branch 52 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 53 (.leaf (-12)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.branch 52 (.branch 49 (.branch 47 (.leaf (-36)) (.branch 48 (.leaf (-33)) (.leaf (-30)))) (.branch 50 (.leaf (-27)) (.branch 51 (.leaf (-24)) (.leaf (-21))))) (.branch 55 (.branch 53 (.leaf (-18)) (.branch 54 (.leaf (-15)) (.leaf (-12)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 18 (.leaf (-7)) (.branch 57 (.leaf (-6)) (.leaf (-3)))),
  (.branch 50 (.branch 46 (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-11))) (.branch 49 (.leaf (-10)) (.leaf (-9))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_161 : Fin 17 → CycleWitness 8 := ![witnessD8_161_1480, witnessD8_161_1481, witnessD8_161_1482, witnessD8_161_1483, witnessD8_161_1484, witnessD8_161_1485, witnessD8_161_1486, witnessD8_161_1487, witnessD8_161_1488, witnessD8_161_1489, witnessD8_161_1490, witnessD8_161_1491, witnessD8_161_1492, witnessD8_161_1493, witnessD8_161_1494, witnessD8_161_1495, witnessD8_161_1496]
end RealPinwheel.FiveSixths


