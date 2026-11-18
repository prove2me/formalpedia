-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_037
-- name    : RealPinwheel_FiveSixths_WitnessD7_037
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:46:24.756634+00:00
-- url     : https://prove2.me/theorems/599d6b1a-6a82-48e2-bd2f-dcc0d9479a20
-- title:
--   Exact witness block D7_037
-- statement:
--   These exact witnesses represent words 494 through 514 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 494–514; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_037_493 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (6)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (5)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (4)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (6)) (.leaf (0)))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (5)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (4)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (2)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_493
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 25 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 26 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.branch 28 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (-8)) (.leaf (-9)))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 38 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-10)) (.leaf (-5)))),
  (.branch 39 (.leaf (-2)) (.branch 45 (.leaf (-1)) (.leaf (0)))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_037_494 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (1)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (5)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 22 (.leaf (6)) (.branch 23 (.leaf (3)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (5)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (4)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (0)))) (.branch 34 (.leaf (6)) (.branch 35 (.leaf (1)) (.leaf (0)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (4)) (.leaf (5)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (0)) (.leaf (1)))) (.branch 46 (.leaf (6)) (.branch 47 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_494
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 25 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 26 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 43 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-14)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 23 (.leaf (-6)) (.branch 32 (.leaf (-7)) (.leaf (-8))))),
  (.branch 8 (.leaf (0)) (.branch 47 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 41 (.branch 31 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 45 (.branch 33 (.leaf (-8)) (.branch 44 (.leaf (-7)) (.leaf (-6)))) (.branch 46 (.leaf (-5)) (.branch 47 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_037_495 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (5)) (.leaf (1)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (0)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (6)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (5))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (1)) (.branch 26 (.leaf (2)) (.leaf (0)))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (1)) (.leaf (4))))) (.branch 33 (.branch 31 (.leaf (6)) (.branch 32 (.leaf (2)) (.leaf (0)))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (4)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (3)))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (1)) (.leaf (4))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (1)))) (.branch 46 (.leaf (3)) (.branch 47 (.leaf (6)) (.leaf (4))))))))
  code := certificateD7_495
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 27 (.leaf (5)) (.leaf (6))) (.branch 38 (.leaf (7)) (.branch 43 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 29 (.leaf (5)) (.leaf (6))) (.branch 41 (.leaf (7)) (.branch 45 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.leaf (-15)))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 29 (.leaf (-7)) (.branch 45 (.leaf (-8)) (.leaf (-9))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 45 (.branch 44 (.leaf (-15)) (.leaf (-12))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-6)) (.leaf (-3))))),
  (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-7)) (.leaf (-5)))),
  (.branch 45 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_037_496 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (2)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (1)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 22 (.leaf (5)) (.branch 23 (.leaf (2)) (.leaf (1))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (3)) (.leaf (1)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (6))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (4)) (.leaf (0)))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (2)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (1)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (3))))) (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 46 (.leaf (6)) (.branch 47 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_496
  counts := ![(.branch 21 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 45 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 44 (.leaf (-1)) (.leaf (0))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_037_497 : CycleWitness 7 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (4)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (0)) (.branch 13 (.leaf (3)) (.leaf (1)))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (1)) (.branch 19 (.leaf (5)) (.leaf (3)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (3))))) (.branch 31 (.branch 29 (.leaf (1)) (.branch 30 (.leaf (0)) (.leaf (4)))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (0)) (.branch 36 (.leaf (3)) (.leaf (1)))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (0))))) (.branch 43 (.branch 41 (.leaf (1)) (.branch 42 (.leaf (6)) (.leaf (3)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_497
  counts := ![(.branch 21 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 32 (.branch 26 (.branch 24 (.leaf (8)) (.leaf (9))) (.branch 30 (.leaf (10)) (.leaf (11)))) (.branch 38 (.branch 35 (.leaf (12)) (.leaf (13))) (.branch 40 (.leaf (14)) (.branch 44 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 45 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 17 (.leaf (-3)) (.branch 40 (.leaf (-4)) (.leaf (-5))))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (-8)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.leaf (-15))),
  (.branch 19 (.leaf (0)) (.leaf (-27))),
  (.branch 42 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 41 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (-3)))),
  (.branch 34 (.branch 26 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-9)))) (.branch 38 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))),
  (.branch 41 (.branch 40 (.leaf (-3)) (.leaf (-2))) (.branch 42 (.leaf (-1)) (.leaf (0)))),
  (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.branch 34 (.branch 32 (.leaf (-15)) (.branch 33 (.leaf (-14)) (.leaf (-13)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-11))) (.branch 37 (.leaf (-10)) (.leaf (-9))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-7))) (.branch 41 (.leaf (-6)) (.leaf (-5)))) (.branch 44 (.branch 43 (.leaf (-4)) (.leaf (-3))) (.branch 45 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 25 (.branch 22 (.branch 20 (.leaf (-27)) (.branch 21 (.leaf (-26)) (.leaf (-25)))) (.branch 23 (.leaf (-24)) (.branch 24 (.leaf (-23)) (.leaf (-22))))) (.branch 28 (.branch 26 (.leaf (-21)) (.branch 27 (.leaf (-20)) (.leaf (-19)))) (.branch 30 (.branch 29 (.leaf (-18)) (.leaf (-17))) (.branch 31 (.leaf (-16)) (.leaf (-15)))))) (.branch 39 (.branch 35 (.branch 33 (.leaf (-14)) (.branch 34 (.leaf (-13)) (.leaf (-12)))) (.branch 37 (.branch 36 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.leaf (-8))))) (.branch 42 (.branch 40 (.leaf (-7)) (.branch 41 (.leaf (-6)) (.leaf (-5)))) (.branch 44 (.branch 43 (.leaf (-4)) (.leaf (-3))) (.branch 45 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 43 (.leaf (-4)) (.leaf (-3))) (.branch 45 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_037_498 : CycleWitness 7 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (5)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (0)) (.branch 13 (.leaf (4)) (.leaf (1)))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (1)) (.branch 19 (.leaf (6)) (.leaf (3)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (4))))) (.branch 31 (.branch 29 (.leaf (1)) (.branch 30 (.leaf (0)) (.leaf (5)))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (0)) (.branch 36 (.leaf (3)) (.leaf (1)))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (0))))) (.branch 43 (.branch 41 (.leaf (1)) (.branch 42 (.leaf (6)) (.leaf (4)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_498
  counts := ![(.branch 21 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 32 (.branch 26 (.branch 24 (.leaf (8)) (.leaf (9))) (.branch 30 (.leaf (10)) (.leaf (11)))) (.branch 38 (.branch 35 (.leaf (12)) (.leaf (13))) (.branch 40 (.leaf (14)) (.branch 44 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 45 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 17 (.leaf (-3)) (.branch 40 (.leaf (-4)) (.leaf (-5))))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (-31)) (.leaf (-32)))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (-7))) (.branch 43 (.leaf (-8)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.leaf (-15))),
  (.branch 19 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 41 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (-3)))),
  (.branch 34 (.branch 26 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-9)))) (.branch 38 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))),
  (.branch 41 (.branch 40 (.leaf (-3)) (.leaf (-2))) (.branch 42 (.leaf (-1)) (.leaf (0)))),
  (.branch 40 (.branch 37 (.branch 21 (.leaf (-32)) (.leaf (-30))) (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-24)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-15)) (.leaf (-12)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.branch 34 (.branch 32 (.leaf (-15)) (.branch 33 (.leaf (-14)) (.leaf (-13)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-11))) (.branch 37 (.leaf (-10)) (.leaf (-9))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-7))) (.branch 41 (.leaf (-6)) (.leaf (-5)))) (.branch 44 (.branch 43 (.leaf (-4)) (.leaf (-3))) (.branch 45 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 44 (.branch 43 (.leaf (-4)) (.leaf (-3))) (.branch 45 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_037_499 : CycleWitness 7 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (4))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (6)))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (5)) (.leaf (3))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (4))))) (.branch 31 (.branch 29 (.leaf (6)) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (0)) (.leaf (2)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (5)))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (6)) (.leaf (3))))))))
  code := certificateD7_499
  counts := ![(.branch 21 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 33 (.branch 26 (.branch 24 (.leaf (8)) (.leaf (9))) (.branch 30 (.leaf (10)) (.leaf (11)))) (.branch 38 (.branch 35 (.leaf (12)) (.leaf (13))) (.branch 41 (.leaf (14)) (.branch 44 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-15)) (.leaf (-17)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 34 (.leaf (-5)) (.leaf (-6)))),
  (.branch 23 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 6 (.leaf (0)) (.leaf (-28))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 45 (.leaf (-4)) (.leaf (-3))),
  (.branch 43 (.branch 37 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-12)) (.branch 45 (.leaf (-8)) (.leaf (-4))))),
  (.branch 44 (.branch 35 (.leaf (-6)) (.leaf (-5))) (.branch 45 (.leaf (-4)) (.leaf (-3)))),
  (.branch 40 (.leaf (-1)) (.leaf (0))),
  (.branch 42 (.branch 29 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-10)))) (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-6))) (.branch 45 (.leaf (-4)) (.leaf (-2))))),
  (.branch 41 (.branch 38 (.branch 7 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-24)) (.branch 40 (.leaf (-21)) (.leaf (-18))))) (.branch 43 (.branch 42 (.leaf (-15)) (.leaf (-12))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 30 (.leaf (-5)) (.leaf (-3)))]
def witnessD7_037_500 : CycleWitness 7 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (0)) (.leaf (4)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (1)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (6)))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (2))))) (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (4)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (5)) (.leaf (3))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (1))))) (.branch 31 (.branch 29 (.leaf (6)) (.branch 30 (.leaf (0)) (.leaf (4)))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (0)) (.leaf (1)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (3)) (.branch 36 (.leaf (0)) (.leaf (5)))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (2))))) (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (4)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (6)) (.leaf (3))))))))
  code := certificateD7_500
  counts := ![(.branch 21 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 33 (.branch 27 (.branch 24 (.leaf (8)) (.leaf (9))) (.branch 30 (.leaf (10)) (.leaf (11)))) (.branch 39 (.branch 36 (.leaf (12)) (.leaf (13))) (.branch 41 (.leaf (14)) (.branch 44 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 25 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 38 (.leaf (8)) (.branch 42 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-15)) (.leaf (-17)))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-5)))) (.branch 28 (.leaf (-6)) (.branch 42 (.leaf (-7)) (.leaf (-8))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 32 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-28))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 42 (.leaf (-17)) (.branch 45 (.leaf (-16)) (.leaf (-8)))),
  (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))),
  (.branch 43 (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 44 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 44 (.branch 32 (.leaf (-7)) (.leaf (-6))) (.branch 45 (.leaf (-4)) (.leaf (-2)))),
  (.branch 41 (.branch 38 (.branch 7 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-24)) (.branch 40 (.leaf (-21)) (.leaf (-18))))) (.branch 43 (.branch 42 (.leaf (-15)) (.leaf (-12))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 30 (.leaf (-5)) (.leaf (-3)))]
def witnessD7_037_501 : CycleWitness 7 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (6)) (.branch 10 (.leaf (0)) (.leaf (1)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (2)))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (5))))) (.branch 20 (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (6))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (4))))) (.branch 31 (.branch 29 (.leaf (1)) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (0)) (.leaf (1)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (3)) (.branch 36 (.leaf (0)) (.leaf (2)))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (6))))) (.branch 43 (.branch 41 (.leaf (1)) (.branch 42 (.leaf (0)) (.leaf (4)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (5))))))))
  code := certificateD7_501
  counts := ![(.branch 21 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 33 (.branch 27 (.branch 24 (.leaf (8)) (.leaf (9))) (.branch 30 (.leaf (10)) (.leaf (11)))) (.branch 39 (.branch 36 (.leaf (12)) (.leaf (13))) (.branch 42 (.leaf (14)) (.branch 44 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 8 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))) (.branch 34 (.branch 29 (.branch 25 (.leaf (7)) (.leaf (8))) (.branch 31 (.leaf (9)) (.leaf (10)))) (.branch 41 (.branch 38 (.leaf (11)) (.leaf (12))) (.branch 45 (.leaf (13)) (.leaf (14)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 21 (.leaf (-15)) (.leaf (-16)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-11)))) (.branch 31 (.leaf (-13)) (.branch 34 (.leaf (-15)) (.leaf (-17))))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-17)) (.leaf (-18)))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (-31))) (.branch 35 (.leaf (-32)) (.leaf (-33)))),
  (.branch 12 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (-7)) (.leaf (-9))))]
  high := ![(.branch 45 (.leaf (-16)) (.leaf (-8))),
  (.branch 35 (.leaf (-17)) (.branch 42 (.leaf (-16)) (.leaf (-13)))),
  (.branch 41 (.branch 39 (.branch 38 (.leaf (-18)) (.leaf (-16))) (.branch 40 (.leaf (-14)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-8))) (.branch 44 (.leaf (-6)) (.branch 45 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 40 (.branch 37 (.branch 36 (.leaf (-33)) (.leaf (-30))) (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-24)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-15)) (.leaf (-12)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 44 (.branch 13 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 42 (.branch 24 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7)))) (.branch 44 (.branch 43 (.leaf (-6)) (.leaf (-5))) (.branch 45 (.leaf (-4)) (.leaf (-3)))))]
def witnessD7_037_502 : CycleWitness 7 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (4)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (1)) (.leaf (0)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (5)) (.branch 13 (.leaf (3)) (.leaf (0)))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (2)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (1)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (6))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (0)) (.leaf (2))))) (.branch 31 (.branch 29 (.leaf (1)) (.branch 30 (.leaf (0)) (.leaf (4)))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (1)) (.leaf (0)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (5)) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (3)) (.leaf (0))))) (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (4)) (.leaf (1)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (3)) (.leaf (6))))))))
  code := certificateD7_502
  counts := ![(.branch 21 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))) (.branch 34 (.branch 27 (.branch 24 (.leaf (7)) (.leaf (8))) (.branch 30 (.leaf (9)) (.leaf (10)))) (.branch 40 (.branch 37 (.leaf (11)) (.leaf (12))) (.branch 44 (.leaf (13)) (.leaf (14)))))),
  (.branch 20 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 25 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 38 (.leaf (8)) (.branch 43 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.leaf (7))))),
  (.branch 26 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 7 (.leaf (-18)) (.leaf (-20)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 10 (.leaf (-10)) (.branch 33 (.leaf (-12)) (.leaf (-13))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))) (.branch 28 (.leaf (-6)) (.branch 41 (.leaf (-7)) (.leaf (-8))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 45 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (-7)) (.leaf (-8)))),
  (.branch 12 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 41 (.branch 31 (.leaf (-20)) (.leaf (-19))) (.branch 45 (.leaf (-14)) (.leaf (-7)))),
  (.branch 39 (.branch 34 (.leaf (-13)) (.leaf (-12))) (.branch 44 (.leaf (-11)) (.branch 45 (.leaf (-8)) (.leaf (-5))))),
  (.branch 43 (.branch 42 (.leaf (-8)) (.leaf (-7))) (.branch 44 (.leaf (-6)) (.branch 45 (.leaf (-5)) (.leaf (-4))))),
  (.leaf (-4)),
  (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-6))) (.branch 45 (.leaf (-4)) (.leaf (-2)))),
  (.branch 40 (.branch 37 (.branch 36 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-8)) (.leaf (-7))))) (.branch 43 (.branch 41 (.leaf (-6)) (.branch 42 (.leaf (-5)) (.leaf (-4)))) (.branch 44 (.leaf (-3)) (.branch 45 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_037_503 : CycleWitness 7 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (2)) (.leaf (0)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (1)) (.leaf (0)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (2)) (.branch 13 (.leaf (1)) (.leaf (0)))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (3)) (.leaf (2))))) (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (5)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (1))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (3))))) (.branch 31 (.branch 29 (.leaf (1)) (.branch 30 (.leaf (2)) (.leaf (0)))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (1)) (.leaf (0)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (2)) (.branch 36 (.leaf (1)) (.leaf (0)))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (3)) (.leaf (2))))) (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (6)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_503
  counts := ![(.branch 21 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))) (.branch 34 (.branch 27 (.branch 24 (.leaf (7)) (.leaf (8))) (.branch 31 (.leaf (9)) (.leaf (10)))) (.branch 41 (.branch 37 (.leaf (11)) (.leaf (12))) (.branch 44 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 29 (.branch 25 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 42 (.branch 38 (.leaf (11)) (.leaf (12))) (.branch 46 (.leaf (13)) (.leaf (14)))))),
  (.branch 22 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 26 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-16)) (.leaf (-18)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 25 (.leaf (-5)) (.branch 38 (.leaf (-6)) (.leaf (-8))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 30 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-13)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-14))),
  (.branch 20 (.leaf (0)) (.leaf (-26))),
  (.branch 43 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 38 (.branch 28 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-14)) (.leaf (-7)))),
  (.branch 43 (.branch 39 (.leaf (-8)) (.leaf (-7))) (.branch 44 (.leaf (-5)) (.branch 45 (.leaf (-3)) (.leaf (-1))))),
  (.branch 36 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 41 (.leaf (-6)) (.leaf (-5)))),
  (.branch 42 (.branch 40 (.leaf (-14)) (.branch 41 (.leaf (-12)) (.leaf (-10)))) (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-6))) (.branch 45 (.leaf (-4)) (.leaf (-2))))),
  (.branch 39 (.branch 35 (.branch 33 (.leaf (-14)) (.branch 34 (.leaf (-13)) (.leaf (-12)))) (.branch 37 (.branch 36 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.leaf (-8))))) (.branch 42 (.branch 40 (.leaf (-7)) (.branch 41 (.leaf (-6)) (.leaf (-5)))) (.branch 44 (.branch 43 (.leaf (-4)) (.leaf (-3))) (.branch 45 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 26 (.branch 23 (.branch 21 (.leaf (-26)) (.branch 22 (.leaf (-25)) (.leaf (-24)))) (.branch 24 (.leaf (-23)) (.branch 25 (.leaf (-22)) (.leaf (-21))))) (.branch 29 (.branch 27 (.leaf (-20)) (.branch 28 (.leaf (-19)) (.leaf (-18)))) (.branch 31 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 32 (.leaf (-15)) (.leaf (-14)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (-13)) (.branch 35 (.leaf (-12)) (.leaf (-11)))) (.branch 37 (.leaf (-10)) (.branch 38 (.leaf (-9)) (.leaf (-8))))) (.branch 42 (.branch 40 (.leaf (-7)) (.branch 41 (.leaf (-6)) (.leaf (-5)))) (.branch 44 (.branch 43 (.leaf (-4)) (.leaf (-3))) (.branch 45 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.leaf (-3)) (.branch 45 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_037_504 : CycleWitness 7 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (5)) (.leaf (4)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (6)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (1)) (.branch 13 (.leaf (3)) (.leaf (0)))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (4))))) (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (5)) (.leaf (1)))) (.branch 21 (.leaf (3)) (.branch 22 (.leaf (2)) (.leaf (0))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (1)) (.leaf (6))) (.branch 26 (.leaf (4)) (.branch 27 (.leaf (2)) (.leaf (0))))) (.branch 31 (.branch 29 (.leaf (3)) (.branch 30 (.leaf (1)) (.leaf (5)))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (1)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (0)))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (2)) (.leaf (6))))) (.branch 43 (.branch 41 (.leaf (5)) (.branch 42 (.leaf (0)) (.leaf (3)))) (.branch 44 (.leaf (1)) (.branch 45 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_504
  counts := ![(.branch 18 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 42 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 24 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 38 (.leaf (8)) (.branch 44 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-16)))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))) (.branch 24 (.leaf (-5)) (.branch 38 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 35 (.leaf (-14)) (.leaf (-20)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (-3))) (.branch 26 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.branch 41 (.leaf (-14)) (.leaf (-17)))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (-5))) (.branch 40 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 43 (.branch 33 (.leaf (-16)) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 44 (.leaf (-11)) (.branch 45 (.leaf (-8)) (.leaf (-5))))),
  (.branch 39 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))),
  (.leaf (-3)),
  (.branch 44 (.branch 36 (.leaf (-20)) (.leaf (-19))) (.branch 45 (.leaf (-14)) (.leaf (-9)))),
  (.branch 37 (.branch 27 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-2)) (.leaf (0)))),
  (.branch 43 (.branch 42 (.leaf (-17)) (.leaf (-14))) (.branch 44 (.leaf (-11)) (.branch 45 (.leaf (-8)) (.leaf (-5))))),
  (.branch 43 (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 44 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (-3)))))]
def witnessD7_037_505 : CycleWitness 7 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (3)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (4)))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (6))))) (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (1)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (3))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (5))))) (.branch 31 (.branch 29 (.leaf (1)) (.branch 30 (.leaf (0)) (.leaf (4)))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (2)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (3)))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (6))))) (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (1)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (4))))))))
  code := certificateD7_505
  counts := ![(.branch 21 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 33 (.branch 27 (.branch 24 (.leaf (8)) (.leaf (9))) (.branch 30 (.leaf (10)) (.leaf (11)))) (.branch 38 (.branch 35 (.leaf (12)) (.leaf (13))) (.branch 41 (.leaf (14)) (.branch 44 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 29 (.branch 25 (.leaf (7)) (.leaf (8))) (.branch 32 (.leaf (9)) (.leaf (10)))) (.branch 43 (.branch 39 (.leaf (11)) (.leaf (12))) (.branch 45 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-15)) (.leaf (-19)))),
  (.branch 22 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 25 (.leaf (-9)) (.branch 45 (.leaf (-11)) (.leaf (-13))))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (-8))) (.branch 37 (.leaf (-9)) (.leaf (-11)))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-18))),
  (.branch 17 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 39 (.branch 36 (.leaf (-19)) (.leaf (-18))) (.branch 42 (.leaf (-17)) (.branch 45 (.leaf (-16)) (.leaf (-8))))),
  (.leaf (-13)),
  (.branch 43 (.branch 27 (.leaf (-14)) (.branch 35 (.leaf (-13)) (.leaf (-12)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3))))),
  (.branch 41 (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8)))) (.branch 43 (.branch 42 (.leaf (-7)) (.leaf (-6))) (.branch 44 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 15 (.leaf (-2)) (.branch 32 (.leaf (-1)) (.leaf (0)))),
  (.branch 37 (.branch 32 (.branch 30 (.branch 29 (.leaf (-18)) (.leaf (-17))) (.branch 31 (.leaf (-16)) (.leaf (-15)))) (.branch 34 (.branch 33 (.leaf (-14)) (.leaf (-13))) (.branch 35 (.leaf (-12)) (.branch 36 (.leaf (-11)) (.leaf (-10)))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-9)) (.leaf (-8))) (.branch 40 (.leaf (-7)) (.leaf (-6)))) (.branch 43 (.branch 42 (.leaf (-5)) (.leaf (-4))) (.branch 44 (.leaf (-3)) (.branch 45 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 41 (.leaf (-6)) (.branch 42 (.leaf (-5)) (.leaf (-4)))) (.branch 44 (.leaf (-3)) (.branch 45 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_037_506 : CycleWitness 7 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (4)) (.branch 7 (.leaf (1)) (.leaf (5)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (3)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (6)))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (1))))) (.branch 20 (.branch 18 (.leaf (4)) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 21 (.leaf (2)) (.branch 22 (.leaf (1)) (.leaf (5))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (2)) (.leaf (0))))) (.branch 31 (.branch 29 (.leaf (4)) (.branch 30 (.leaf (1)) (.leaf (6)))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (3)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (5)))) (.branch 38 (.leaf (2)) (.branch 39 (.leaf (0)) (.leaf (1))))) (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (3)) (.leaf (0)))) (.branch 44 (.leaf (2)) (.branch 45 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_506
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 25 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.branch 25 (.leaf (-11)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (-8))) (.branch 37 (.leaf (-9)) (.leaf (-11)))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 44 (.branch 40 (.leaf (-19)) (.leaf (-18))) (.branch 45 (.leaf (-12)) (.leaf (-6)))),
  (.branch 31 (.branch 26 (.leaf (-14)) (.leaf (-13))) (.branch 36 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10))))),
  (.branch 39 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-4)))),
  (.branch 43 (.branch 27 (.leaf (-14)) (.branch 35 (.leaf (-13)) (.leaf (-12)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3))))),
  (.branch 43 (.branch 30 (.leaf (-11)) (.branch 42 (.leaf (-10)) (.leaf (-8)))) (.branch 44 (.leaf (-6)) (.branch 45 (.leaf (-4)) (.leaf (-2))))),
  (.branch 41 (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8)))) (.branch 43 (.branch 42 (.leaf (-7)) (.leaf (-6))) (.branch 44 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 15 (.leaf (-2)) (.branch 32 (.leaf (-1)) (.leaf (0))))]
def witnessD7_037_507 : CycleWitness 7 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (5)) (.leaf (3)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (1)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (2)))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (1)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 21 (.leaf (1)) (.branch 22 (.leaf (5)) (.leaf (2))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (4)) (.branch 27 (.leaf (2)) (.leaf (0))))) (.branch 31 (.branch 29 (.leaf (1)) (.branch 30 (.leaf (6)) (.leaf (3)))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (1)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (4)) (.branch 36 (.leaf (0)) (.leaf (2)))) (.branch 38 (.leaf (5)) (.branch 39 (.leaf (1)) (.leaf (0))))) (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (0)))) (.branch 44 (.leaf (1)) (.branch 45 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_507
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 25 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 39 (.leaf (8)) (.branch 44 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 41 (.leaf (8)) (.branch 46 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 29 (.leaf (-10)) (.leaf (-11)))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 27 (.leaf (-2)) (.branch 41 (.leaf (-3)) (.leaf (-4))))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (-7)) (.leaf (-8)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 35 (.leaf (-14)) (.leaf (-17)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (-25)) (.leaf (-26)))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (-1))) (.branch 45 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 44 (.leaf (-18)) (.branch 45 (.leaf (-12)) (.leaf (-6)))),
  (.branch 35 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-5))))),
  (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.branch 45 (.leaf (-1)) (.leaf (0))))),
  (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-6))) (.branch 45 (.leaf (-4)) (.leaf (-2)))),
  (.branch 40 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13))))) (.branch 43 (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7)))))),
  (.branch 41 (.branch 39 (.branch 23 (.leaf (-26)) (.leaf (-24))) (.branch 40 (.leaf (-21)) (.leaf (-18)))) (.branch 43 (.branch 42 (.leaf (-15)) (.leaf (-12))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (-3))]
def witnessD7_037_508 : CycleWitness 7 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (6)) (.branch 7 (.leaf (1)) (.leaf (3)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (4)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (1)) (.branch 13 (.leaf (5)) (.leaf (2)))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (1))))) (.branch 20 (.branch 18 (.leaf (4)) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 21 (.leaf (6)) (.branch 22 (.leaf (1)) (.leaf (3))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (4)) (.branch 27 (.leaf (1)) (.leaf (0))))) (.branch 31 (.branch 29 (.leaf (5)) (.branch 30 (.leaf (2)) (.leaf (3)))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (4)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (2)) (.branch 36 (.leaf (6)) (.leaf (1)))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (2))))) (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (0)) (.leaf (1)))) (.branch 44 (.leaf (5)) (.branch 45 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_508
  counts := ![(.branch 19 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 24 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 38 (.leaf (8)) (.branch 42 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 27 (.leaf (5)) (.leaf (6))) (.branch 37 (.leaf (7)) (.branch 43 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 40 (.leaf (7)) (.branch 45 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-18)) (.leaf (-21)))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-28))) (.branch 12 (.leaf (-29)) (.leaf (-30)))) (.branch 27 (.branch 22 (.leaf (-31)) (.leaf (-32))) (.branch 32 (.leaf (-33)) (.branch 37 (.leaf (-34)) (.leaf (-35)))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 14 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-14)) (.leaf (-15)))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (-28))) (.branch 36 (.leaf (-29)) (.leaf (-30))))]
  high := ![(.branch 43 (.branch 29 (.leaf (-21)) (.leaf (-20))) (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-10)) (.leaf (-5))))),
  (.branch 44 (.branch 38 (.leaf (-35)) (.leaf (-27))) (.branch 45 (.leaf (-18)) (.leaf (-9)))),
  (.branch 15 (.leaf (-12)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 43 (.branch 42 (.leaf (-15)) (.leaf (-12))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-3)))),
  (.branch 41 (.branch 38 (.branch 37 (.leaf (-30)) (.leaf (-27))) (.branch 39 (.leaf (-24)) (.branch 40 (.leaf (-21)) (.leaf (-18))))) (.branch 43 (.branch 42 (.leaf (-15)) (.leaf (-12))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3))))))]
def witnessD7_037_509 : CycleWitness 7 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (6)) (.branch 10 (.leaf (2)) (.leaf (0)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (4)) (.branch 13 (.leaf (1)) (.leaf (3)))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (5)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 21 (.leaf (3)) (.branch 22 (.leaf (2)) (.leaf (4))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (6)) (.branch 27 (.leaf (0)) (.leaf (2))))) (.branch 31 (.branch 29 (.leaf (3)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (2)) (.leaf (0)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (4)) (.branch 36 (.leaf (1)) (.leaf (3)))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (0))))) (.branch 43 (.branch 41 (.leaf (6)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 44 (.leaf (3)) (.branch 45 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_509
  counts := ![(.branch 20 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))) (.branch 34 (.branch 27 (.branch 24 (.leaf (7)) (.leaf (8))) (.branch 31 (.leaf (9)) (.leaf (10)))) (.branch 40 (.branch 38 (.leaf (11)) (.leaf (12))) (.branch 43 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-12)) (.leaf (-14)))) (.branch 40 (.branch 20 (.leaf (-17)) (.leaf (-19))) (.branch 43 (.leaf (-21)) (.leaf (-23))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-15)) (.leaf (-18)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-3)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 32 (.leaf (-14)) (.leaf (-16)))),
  (.branch 9 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 44 (.leaf (-23)) (.branch 45 (.leaf (-18)) (.leaf (-13)))),
  (.branch 43 (.branch 31 (.leaf (-18)) (.branch 37 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.leaf (-12)) (.branch 45 (.leaf (-8)) (.leaf (-4))))),
  (.branch 34 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))),
  (.branch 45 (.leaf (-6)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 39 (.branch 35 (.branch 33 (.leaf (-16)) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 37 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.leaf (-10))))) (.branch 42 (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7)))) (.branch 44 (.branch 43 (.leaf (-6)) (.leaf (-5))) (.branch 45 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 43 (.branch 42 (.leaf (-7)) (.leaf (-6))) (.branch 44 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (-3)))))]
def witnessD7_037_510 : CycleWitness 7 where
  length := 45
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 8 (.branch 7 (.leaf (2)) (.leaf (0))) (.branch 9 (.leaf (1)) (.leaf (0))))) (.branch 17 (.branch 15 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (3)) (.leaf (0)))) (.branch 21 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (1)) (.leaf (0)))))) (.branch 34 (.branch 27 (.branch 25 (.leaf (4)) (.branch 26 (.leaf (0)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.leaf (5))))) (.branch 40 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (6))) (.branch 44 (.leaf (0)) (.leaf (1)))))))
  code := certificateD7_510
  counts := ![(.branch 21 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (5)) (.leaf (6))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (7)) (.leaf (8))) (.branch 14 (.leaf (9)) (.leaf (10)))) (.branch 19 (.branch 17 (.leaf (11)) (.leaf (12))) (.branch 20 (.leaf (13)) (.leaf (14)))))) (.branch 33 (.branch 28 (.branch 24 (.branch 23 (.leaf (15)) (.leaf (16))) (.branch 26 (.leaf (17)) (.leaf (18)))) (.branch 30 (.branch 29 (.leaf (19)) (.leaf (20))) (.branch 32 (.leaf (21)) (.leaf (22))))) (.branch 39 (.branch 37 (.branch 35 (.leaf (23)) (.leaf (24))) (.branch 38 (.leaf (25)) (.leaf (26)))) (.branch 42 (.branch 41 (.leaf (27)) (.leaf (28))) (.branch 44 (.leaf (29)) (.leaf (30))))))),
  (.branch 22 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 27 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-1))) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-38))),
  (.branch 16 (.leaf (0)) (.leaf (-29))),
  (.branch 25 (.leaf (0)) (.leaf (-20))),
  (.branch 34 (.leaf (0)) (.leaf (-11))),
  (.branch 43 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 43 (.leaf (-3)) (.leaf (-2))),
  (.branch 41 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.branch 16 (.branch 11 (.branch 9 (.branch 8 (.leaf (-38)) (.leaf (-37))) (.branch 10 (.leaf (-36)) (.leaf (-35)))) (.branch 13 (.branch 12 (.leaf (-34)) (.leaf (-33))) (.branch 14 (.leaf (-32)) (.branch 15 (.leaf (-31)) (.leaf (-30)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-29)) (.leaf (-28))) (.branch 19 (.leaf (-27)) (.branch 20 (.leaf (-26)) (.leaf (-25))))) (.branch 23 (.branch 22 (.leaf (-24)) (.leaf (-23))) (.branch 24 (.leaf (-22)) (.branch 25 (.leaf (-21)) (.leaf (-20))))))) (.branch 35 (.branch 30 (.branch 28 (.branch 27 (.leaf (-19)) (.leaf (-18))) (.branch 29 (.leaf (-17)) (.leaf (-16)))) (.branch 32 (.branch 31 (.leaf (-15)) (.leaf (-14))) (.branch 33 (.leaf (-13)) (.branch 34 (.leaf (-12)) (.leaf (-11)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6))))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 30 (.branch 23 (.branch 19 (.branch 17 (.leaf (-29)) (.branch 18 (.leaf (-28)) (.leaf (-27)))) (.branch 21 (.branch 20 (.leaf (-26)) (.leaf (-25))) (.branch 22 (.leaf (-24)) (.leaf (-23))))) (.branch 26 (.branch 24 (.leaf (-22)) (.branch 25 (.leaf (-21)) (.leaf (-20)))) (.branch 28 (.branch 27 (.leaf (-19)) (.leaf (-18))) (.branch 29 (.leaf (-17)) (.leaf (-16)))))) (.branch 37 (.branch 33 (.branch 31 (.leaf (-15)) (.branch 32 (.leaf (-14)) (.leaf (-13)))) (.branch 35 (.branch 34 (.leaf (-12)) (.leaf (-11))) (.branch 36 (.leaf (-10)) (.leaf (-9))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 30 (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-19))) (.branch 28 (.leaf (-18)) (.branch 29 (.leaf (-17)) (.leaf (-16))))) (.branch 32 (.branch 31 (.leaf (-15)) (.leaf (-14))) (.branch 33 (.leaf (-13)) (.branch 34 (.leaf (-12)) (.leaf (-11)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6))))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.branch 36 (.branch 35 (.leaf (-11)) (.leaf (-10))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7))))) (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 44 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_037_511 : CycleWitness 7 where
  length := 45
  word := (.branch 23 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 8 (.branch 7 (.leaf (2)) (.leaf (0))) (.branch 9 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (1))))))) (.branch 34 (.branch 29 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (0))))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (5)))))) (.branch 40 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (0))))) (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (6)) (.branch 44 (.leaf (0)) (.leaf (1))))))))
  code := certificateD7_511
  counts := ![(.branch 22 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 15 (.branch 11 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))) (.branch 19 (.branch 17 (.leaf (9)) (.leaf (10))) (.branch 20 (.leaf (11)) (.leaf (12)))))) (.branch 33 (.branch 28 (.branch 24 (.leaf (13)) (.branch 26 (.leaf (14)) (.leaf (15)))) (.branch 29 (.leaf (16)) (.branch 31 (.leaf (17)) (.leaf (18))))) (.branch 38 (.branch 35 (.leaf (19)) (.branch 37 (.leaf (20)) (.leaf (21)))) (.branch 42 (.branch 40 (.leaf (22)) (.leaf (23))) (.branch 44 (.leaf (24)) (.leaf (25))))))),
  (.branch 23 (.branch 12 (.branch 5 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 32 (.leaf (10)) (.leaf (11)))) (.branch 41 (.branch 39 (.leaf (12)) (.leaf (13))) (.branch 45 (.leaf (14)) (.leaf (15)))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-38))),
  (.branch 16 (.leaf (0)) (.leaf (-29))),
  (.branch 25 (.leaf (0)) (.leaf (-20))),
  (.branch 34 (.leaf (0)) (.leaf (-11))),
  (.branch 43 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 41 (.branch 39 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.branch 16 (.branch 11 (.branch 9 (.branch 8 (.leaf (-38)) (.leaf (-37))) (.branch 10 (.leaf (-36)) (.leaf (-35)))) (.branch 13 (.branch 12 (.leaf (-34)) (.leaf (-33))) (.branch 14 (.leaf (-32)) (.branch 15 (.leaf (-31)) (.leaf (-30)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-29)) (.leaf (-28))) (.branch 19 (.leaf (-27)) (.branch 20 (.leaf (-26)) (.leaf (-25))))) (.branch 23 (.branch 22 (.leaf (-24)) (.leaf (-23))) (.branch 24 (.leaf (-22)) (.branch 25 (.leaf (-21)) (.leaf (-20))))))) (.branch 35 (.branch 30 (.branch 28 (.branch 27 (.leaf (-19)) (.leaf (-18))) (.branch 29 (.leaf (-17)) (.leaf (-16)))) (.branch 32 (.branch 31 (.leaf (-15)) (.leaf (-14))) (.branch 33 (.leaf (-13)) (.branch 34 (.leaf (-12)) (.leaf (-11)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6))))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 30 (.branch 23 (.branch 19 (.branch 17 (.leaf (-29)) (.branch 18 (.leaf (-28)) (.leaf (-27)))) (.branch 21 (.branch 20 (.leaf (-26)) (.leaf (-25))) (.branch 22 (.leaf (-24)) (.leaf (-23))))) (.branch 26 (.branch 24 (.leaf (-22)) (.branch 25 (.leaf (-21)) (.leaf (-20)))) (.branch 28 (.branch 27 (.leaf (-19)) (.leaf (-18))) (.branch 29 (.leaf (-17)) (.leaf (-16)))))) (.branch 37 (.branch 33 (.branch 31 (.leaf (-15)) (.branch 32 (.leaf (-14)) (.leaf (-13)))) (.branch 35 (.branch 34 (.leaf (-12)) (.leaf (-11))) (.branch 36 (.leaf (-10)) (.leaf (-9))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 30 (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-19))) (.branch 28 (.leaf (-18)) (.branch 29 (.leaf (-17)) (.leaf (-16))))) (.branch 32 (.branch 31 (.leaf (-15)) (.leaf (-14))) (.branch 33 (.leaf (-13)) (.branch 34 (.leaf (-12)) (.leaf (-11)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6))))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.branch 36 (.branch 35 (.leaf (-11)) (.leaf (-10))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7))))) (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 44 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_037_512 : CycleWitness 7 where
  length := 45
  word := (.branch 23 (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (0))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 17 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (5)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (6)) (.leaf (0))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (3)) (.leaf (0))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (0)))))) (.branch 39 (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (5)) (.branch 38 (.leaf (0)) (.leaf (3))))) (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (0)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_512
  counts := ![(.branch 21 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 16 (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))) (.branch 17 (.leaf (9)) (.branch 19 (.leaf (10)) (.leaf (11)))))) (.branch 32 (.branch 27 (.branch 23 (.leaf (12)) (.branch 25 (.leaf (13)) (.leaf (14)))) (.branch 29 (.leaf (15)) (.branch 31 (.leaf (16)) (.leaf (17))))) (.branch 38 (.branch 34 (.leaf (18)) (.branch 36 (.leaf (19)) (.leaf (20)))) (.branch 42 (.branch 40 (.leaf (21)) (.leaf (22))) (.branch 44 (.leaf (23)) (.leaf (24))))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 15 (.leaf (0)) (.branch 37 (.leaf (-15)) (.leaf (-16)))),
  (.branch 22 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 37 (.branch 33 (.leaf (-14)) (.branch 35 (.leaf (-13)) (.leaf (-12)))) (.branch 41 (.branch 39 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.leaf (-8))))),
  (.branch 36 (.leaf (-5)) (.branch 44 (.leaf (-4)) (.leaf (-2)))),
  (.branch 42 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))),
  (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 37 (.branch 33 (.branch 31 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 32 (.leaf (-28)) (.leaf (-26)))) (.branch 35 (.branch 34 (.leaf (-24)) (.leaf (-22))) (.branch 36 (.leaf (-20)) (.leaf (-18))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-16)) (.leaf (-14))) (.branch 40 (.leaf (-12)) (.leaf (-10)))) (.branch 43 (.branch 42 (.leaf (-8)) (.leaf (-6))) (.branch 44 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 41 (.branch 39 (.branch 38 (.leaf (-16)) (.leaf (-14))) (.branch 40 (.leaf (-12)) (.leaf (-10)))) (.branch 43 (.branch 42 (.leaf (-8)) (.leaf (-6))) (.branch 44 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.leaf (-1)) (.leaf (0)))]
def witnessD7_037_513 : CycleWitness 7 where
  length := 45
  word := (.branch 23 (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 8 (.branch 7 (.leaf (2)) (.leaf (0))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (4)))))) (.branch 17 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (3)) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (0))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (5)) (.branch 27 (.leaf (0)) (.leaf (2))))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (3)) (.leaf (0)))))) (.branch 39 (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (1))))) (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (6)) (.leaf (0)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (1))))))))
  code := certificateD7_513
  counts := ![(.branch 21 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 16 (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))) (.branch 17 (.leaf (9)) (.branch 19 (.leaf (10)) (.leaf (11)))))) (.branch 32 (.branch 27 (.branch 23 (.leaf (12)) (.branch 25 (.leaf (13)) (.leaf (14)))) (.branch 29 (.leaf (15)) (.branch 31 (.leaf (16)) (.leaf (17))))) (.branch 38 (.branch 34 (.leaf (18)) (.branch 36 (.leaf (19)) (.leaf (20)))) (.branch 42 (.branch 40 (.leaf (21)) (.leaf (22))) (.branch 44 (.leaf (23)) (.leaf (24))))))),
  (.branch 24 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 39 (.leaf (7)) (.branch 45 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 28 (.leaf (-3)) (.branch 43 (.leaf (-4)) (.leaf (-5))))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-34))),
  (.branch 26 (.leaf (0)) (.leaf (-19))),
  (.branch 41 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 37 (.branch 33 (.leaf (-14)) (.branch 35 (.leaf (-13)) (.leaf (-12)))) (.branch 41 (.branch 39 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.leaf (-8))))),
  (.branch 40 (.leaf (-1)) (.leaf (0))),
  (.branch 44 (.leaf (-5)) (.leaf (-4))),
  (.branch 39 (.branch 36 (.branch 34 (.leaf (-12)) (.branch 35 (.leaf (-11)) (.leaf (-10)))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7))))) (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-34)) (.leaf (-33))) (.branch 14 (.leaf (-32)) (.leaf (-31)))) (.branch 17 (.branch 16 (.leaf (-30)) (.leaf (-29))) (.branch 18 (.leaf (-28)) (.leaf (-27))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-26)) (.leaf (-25))) (.branch 22 (.leaf (-24)) (.leaf (-23)))) (.branch 25 (.branch 24 (.leaf (-22)) (.leaf (-21))) (.branch 26 (.leaf (-20)) (.branch 27 (.leaf (-19)) (.leaf (-18))))))) (.branch 36 (.branch 32 (.branch 30 (.branch 29 (.leaf (-17)) (.leaf (-16))) (.branch 31 (.leaf (-15)) (.leaf (-14)))) (.branch 34 (.branch 33 (.leaf (-13)) (.leaf (-12))) (.branch 35 (.leaf (-11)) (.leaf (-10))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-8))) (.branch 39 (.leaf (-7)) (.leaf (-6)))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 35 (.branch 30 (.branch 28 (.branch 27 (.leaf (-19)) (.leaf (-18))) (.branch 29 (.leaf (-17)) (.leaf (-16)))) (.branch 32 (.branch 31 (.leaf (-15)) (.leaf (-14))) (.branch 33 (.leaf (-13)) (.branch 34 (.leaf (-12)) (.leaf (-11)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6))))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_037 : Fin 21 → CycleWitness 7 := ![witnessD7_037_493, witnessD7_037_494, witnessD7_037_495, witnessD7_037_496, witnessD7_037_497, witnessD7_037_498, witnessD7_037_499, witnessD7_037_500, witnessD7_037_501, witnessD7_037_502, witnessD7_037_503, witnessD7_037_504, witnessD7_037_505, witnessD7_037_506, witnessD7_037_507, witnessD7_037_508, witnessD7_037_509, witnessD7_037_510, witnessD7_037_511, witnessD7_037_512, witnessD7_037_513]
end RealPinwheel.FiveSixths


