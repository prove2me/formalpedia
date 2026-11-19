-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_301
-- name    : RealPinwheel_FiveSixths_WitnessP9_301
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:27:04.078033+00:00
-- url     : https://prove2.me/theorems/5df6aab0-9791-4362-bc0b-b63aa8e27e3d
-- title:
--   Exact witness block P9_301
-- statement:
--   These exact witnesses represent words 5466 through 5516 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 5466–5516; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_301_5465 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (1))) (.branch 6 (.leaf (5)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (6)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (8)) (.leaf (4))) (.branch 14 (.leaf (3)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (2)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (7)) (.leaf (6))) (.branch 21 (.leaf (0)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (5)))) (.branch 28 (.branch 27 (.leaf (8)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (2)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (7)) (.leaf (0))) (.branch 36 (.leaf (5)) (.leaf (3))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (2))) (.branch 40 (.leaf (6)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (8)) (.leaf (4))) (.branch 44 (.leaf (3)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (5)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (7)) (.leaf (6))) (.branch 51 (.leaf (1)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (5)))) (.branch 58 (.branch 57 (.leaf (8)) (.leaf (1))) (.branch 59 (.leaf (3)) (.leaf (6))))))))
  code := certificateP9_5465
  counts := ![(.branch 28 (.branch 8 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 58 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 56 (.branch 42 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 58 (.branch 57 (.leaf (-12)) (.leaf (-9))) (.branch 59 (.leaf (-6)) (.leaf (-3))))),
  (.branch 52 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-10)) (.leaf (-8)))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_301_5466 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (5)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (4)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (5)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (4)) (.leaf (7))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (5)))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 40 (.leaf (5)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (3))) (.branch 44 (.leaf (4)) (.leaf (6)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (4))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (5)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (4)) (.leaf (8))))))))
  code := certificateP9_5466
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 60 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-11)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.branch 30 (.leaf (0)) (.leaf (-30))),
  (.leaf (0))]
  high := ![(.branch 58 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 59 (.leaf (-8)) (.leaf (-4)))),
  (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-6))) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-10)) (.leaf (-8)))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 59 (.leaf (-4)) (.leaf (-2))),
  (.leaf (-2)),
  (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28)))) (.branch 35 (.branch 34 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-25)) (.leaf (-24))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.leaf (-20)))) (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_301_5467 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (3))) (.branch 6 (.leaf (7)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (6))) (.branch 10 (.leaf (2)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (5))) (.branch 14 (.leaf (0)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (8)) (.branch 17 (.leaf (2)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (6)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (7)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (6)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (2)) (.leaf (5)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (8)) (.leaf (4))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (6))) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (3)) (.leaf (5))) (.branch 44 (.leaf (1)) (.leaf (4)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (7)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (6)) (.leaf (3))) (.branch 51 (.leaf (1)) (.leaf (4))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (8)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (6)) (.leaf (4))))))))
  code := certificateP9_5467
  counts := ![(.branch 28 (.branch 8 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 58 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 14 (.leaf (-17)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 57 (.branch 55 (.leaf (-18)) (.branch 56 (.leaf (-15)) (.leaf (-12)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3))))),
  (.branch 52 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 57 (.branch 48 (.leaf (-11)) (.branch 56 (.leaf (-10)) (.leaf (-8)))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_301_5468 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (6)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (2))) (.branch 10 (.leaf (4)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (8)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (2)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (7))) (.branch 21 (.leaf (4)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (1))) (.branch 29 (.leaf (8)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (7)))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (6)) (.leaf (2))) (.branch 40 (.leaf (4)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (5)) (.leaf (0))) (.branch 44 (.leaf (8)) (.leaf (7)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (2)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (6))) (.branch 51 (.leaf (4)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (7)) (.leaf (1))) (.branch 59 (.leaf (8)) (.leaf (4))))))))
  code := certificateP9_5468
  counts := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))) (.branch 52 (.branch 28 (.leaf (-10)) (.leaf (-11))) (.branch 58 (.leaf (-15)) (.leaf (-16))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 42 (.leaf (-18)) (.leaf (-21)))),
  (.branch 3 (.leaf (0)) (.branch 38 (.leaf (-9)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-16)) (.leaf (-13))),
  (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-10)) (.leaf (-8)))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 56 (.branch 54 (.branch 43 (.leaf (-21)) (.leaf (-20))) (.branch 55 (.leaf (-18)) (.leaf (-16)))) (.branch 58 (.branch 57 (.leaf (-14)) (.leaf (-12))) (.branch 59 (.leaf (-10)) (.leaf (-8))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1))]
def witnessP9_301_5469 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (6))) (.branch 10 (.leaf (7)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (8)) (.leaf (1))) (.branch 14 (.leaf (3)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (0)) (.leaf (7))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (8))) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (6)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (7)) (.leaf (0))) (.branch 36 (.leaf (8)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (4)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (5)) (.leaf (1))) (.branch 44 (.leaf (6)) (.leaf (0)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (7)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (8)) (.leaf (3))) (.branch 51 (.leaf (0)) (.leaf (4))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (5))) (.branch 55 (.leaf (0)) (.leaf (6)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (7)) (.leaf (8))))))))
  code := certificateP9_5469
  counts := ![(.branch 28 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))) (.branch 45 (.branch 35 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 48 (.leaf (14)) (.leaf (15))) (.branch 55 (.leaf (16)) (.branch 58 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 2 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.leaf (0))]
  high := ![(.branch 52 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0))]
def witnessP9_301_5470 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (7)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (5))) (.branch 14 (.leaf (2)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (8)) (.leaf (0))) (.branch 21 (.leaf (6)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (2)) (.leaf (7))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (0))) (.branch 36 (.leaf (6)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (3)) (.leaf (0))) (.branch 40 (.leaf (8)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (5))) (.branch 44 (.leaf (2)) (.leaf (4)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (7)) (.leaf (0))) (.branch 51 (.leaf (6)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (5))) (.branch 59 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_5470
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 23 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-6)) (.leaf (-8)))) (.branch 38 (.leaf (-9)) (.branch 53 (.leaf (-10)) (.leaf (-11))))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.branch 49 (.leaf (-10)) (.leaf (-11)))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-8)) (.leaf (-4)))),
  (.branch 57 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 56 (.branch 54 (.leaf (-11)) (.branch 55 (.leaf (-10)) (.leaf (-9)))) (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5))))),
  (.branch 57 (.branch 35 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.leaf (-1)) (.leaf (0)))]
def witnessP9_301_5471 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (0))) (.branch 10 (.leaf (5)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (2)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (8)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (0))) (.branch 21 (.leaf (6)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (7))) (.branch 29 (.leaf (2)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (0))) (.branch 36 (.leaf (6)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (8)) (.leaf (0))) (.branch 40 (.leaf (5)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (3))) (.branch 44 (.leaf (2)) (.leaf (4)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (7)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (5)) (.leaf (0))) (.branch 51 (.leaf (6)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (8))) (.branch 59 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_5471
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 2 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.branch 47 (.leaf (-12)) (.leaf (-13)))),
  (.branch 17 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-8)) (.leaf (-4)))),
  (.branch 57 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 56 (.branch 54 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 57 (.branch 35 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.leaf (-1)) (.leaf (0))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_301_5472 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (2))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (6)) (.leaf (8))) (.branch 10 (.leaf (1)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (2)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (6)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (2))) (.branch 21 (.leaf (4)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (7))) (.branch 25 (.leaf (1)) (.leaf (6)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (2)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (5)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (2))) (.branch 36 (.leaf (3)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (4)) (.leaf (8))) (.branch 40 (.leaf (1)) (.leaf (5)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (6))) (.branch 44 (.leaf (2)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (5)) (.leaf (2))) (.branch 51 (.leaf (6)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (7))) (.branch 55 (.leaf (1)) (.leaf (4)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (5))) (.branch 59 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_5472
  counts := ![(.branch 27 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.leaf (7))))),
  (.branch 34 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 35 (.leaf (-4)) (.branch 50 (.leaf (-5)) (.leaf (-6))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-46))) (.branch 36 (.leaf (-47)) (.branch 53 (.leaf (-48)) (.leaf (-49))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (-32))) (.branch 38 (.leaf (-33)) (.leaf (-34)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-18)) (.leaf (-19)))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 24 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-21)))]
  high := ![(.branch 58 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 51 (.leaf (-6)) (.leaf (-5))),
  (.branch 56 (.branch 54 (.leaf (-49)) (.branch 55 (.leaf (-42)) (.leaf (-35)))) (.branch 58 (.branch 57 (.leaf (-28)) (.leaf (-21))) (.branch 59 (.leaf (-14)) (.leaf (-7))))),
  (.branch 57 (.branch 39 (.leaf (-34)) (.branch 48 (.leaf (-31)) (.leaf (-28)))) (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-14)) (.leaf (-7))))),
  (.branch 50 (.branch 24 (.leaf (-19)) (.leaf (-17))) (.branch 59 (.leaf (-14)) (.leaf (-7)))),
  (.branch 9 (.leaf (-4)) (.branch 52 (.leaf (-3)) (.leaf (0)))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 44 (.branch 41 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17))))) (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_301_5473 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (1))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (1))) (.branch 14 (.leaf (5)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (7))) (.branch 21 (.leaf (0)) (.leaf (5))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (3)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (1))) (.branch 29 (.leaf (5)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (6))) (.branch 36 (.leaf (0)) (.leaf (5))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (1))) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (1))) (.branch 44 (.leaf (5)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (8))) (.branch 51 (.leaf (0)) (.leaf (5))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (1))) (.branch 55 (.leaf (3)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (4)) (.leaf (1))) (.branch 59 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_5473
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 13 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 5 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-25))),
  (.branch 20 (.leaf (0)) (.leaf (-40))),
  (.branch 50 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 57 (.branch 48 (.leaf (-11)) (.branch 56 (.leaf (-10)) (.leaf (-8)))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 58 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 47 (.branch 41 (.branch 38 (.branch 36 (.leaf (-25)) (.branch 37 (.leaf (-24)) (.leaf (-23)))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))) (.branch 44 (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17)))) (.branch 45 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-40)) (.leaf (-39))) (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36))))) (.branch 27 (.branch 26 (.leaf (-35)) (.leaf (-34))) (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-27)) (.leaf (-26))))) (.branch 37 (.branch 36 (.leaf (-25)) (.leaf (-24))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))))) (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_301_5474 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (8)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (6))) (.branch 10 (.leaf (0)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (7))) (.branch 14 (.leaf (0)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (4)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (8)) (.leaf (1))) (.branch 21 (.leaf (6)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (7))) (.branch 25 (.leaf (2)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (1)) (.leaf (8))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (0))) (.branch 36 (.leaf (7)) (.leaf (4))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (5))) (.branch 40 (.leaf (0)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (8))) (.branch 44 (.leaf (0)) (.leaf (6)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (4)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (7)) (.leaf (2))) (.branch 51 (.leaf (5)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (8))) (.branch 55 (.leaf (1)) (.leaf (4)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (6))) (.branch 59 (.leaf (2)) (.leaf (7))))))))
  code := certificateP9_5474
  counts := ![(.branch 27 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 44 (.branch 35 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 40 (.leaf (9)) (.leaf (10)))) (.branch 53 (.branch 48 (.leaf (11)) (.leaf (12))) (.branch 57 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 13 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-23)) (.leaf (-25)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-39)) (.leaf (-40)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (-4))) (.branch 33 (.leaf (-8)) (.branch 50 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 49 (.branch 36 (.leaf (-25)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-14)) (.leaf (-7))))),
  (.branch 56 (.branch 21 (.leaf (-40)) (.branch 47 (.leaf (-38)) (.leaf (-35)))) (.branch 58 (.branch 57 (.leaf (-28)) (.leaf (-21))) (.branch 59 (.leaf (-14)) (.leaf (-7))))),
  (.branch 51 (.leaf (-10)) (.leaf (-7))),
  (.branch 55 (.branch 53 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_301_5475 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (3))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (2))) (.branch 14 (.leaf (6)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (5))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (3))) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (2))) (.branch 29 (.leaf (7)) (.leaf (1))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (5))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (3))) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (2))) (.branch 44 (.leaf (6)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (5))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (3))) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (4)) (.leaf (2))) (.branch 59 (.leaf (8)) (.leaf (1))))))))
  code := certificateP9_5475
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 59 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 14 (.leaf (0)) (.leaf (-16))),
  (.branch 29 (.leaf (0)) (.leaf (-31))),
  (.branch 59 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-10)) (.leaf (-8)))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 58 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (-31)) (.branch 31 (.leaf (-30)) (.leaf (-29)))) (.branch 34 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 35 (.leaf (-26)) (.leaf (-25))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-23))) (.branch 39 (.leaf (-22)) (.leaf (-21)))) (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.leaf (-17)))))) (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_301_5476 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (6))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (3))) (.branch 10 (.leaf (4)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (5))) (.branch 14 (.leaf (0)) (.leaf (8)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (6))) (.branch 21 (.leaf (0)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (7)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (3)) (.leaf (8))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (2)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (6))) (.branch 36 (.leaf (3)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (7)) (.leaf (2))) (.branch 40 (.leaf (4)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (3)) (.leaf (5))) (.branch 44 (.leaf (1)) (.leaf (8)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (6))) (.branch 51 (.leaf (1)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (7)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (5))) (.branch 59 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_5476
  counts := ![(.branch 27 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 37 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 57 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 59 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 56 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 7 (.leaf (-17)) (.leaf (-19)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-8)) (.leaf (-9)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 56 (.branch 48 (.leaf (-19)) (.branch 55 (.leaf (-18)) (.leaf (-15)))) (.branch 58 (.branch 57 (.leaf (-12)) (.leaf (-9))) (.branch 59 (.leaf (-6)) (.leaf (-3))))),
  (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 57 (.branch 43 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessP9_301_5477 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (8))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (3))) (.branch 10 (.leaf (4)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (6))) (.branch 14 (.leaf (0)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (7))) (.branch 21 (.leaf (0)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (3)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (2)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (8))) (.branch 36 (.leaf (3)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (5)) (.leaf (2))) (.branch 40 (.leaf (4)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (3)) (.leaf (6))) (.branch 44 (.leaf (1)) (.leaf (5)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (7))) (.branch 51 (.leaf (1)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (6))) (.branch 59 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_5477
  counts := ![(.branch 27 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 37 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 57 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 59 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 56 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 7 (.leaf (-17)) (.leaf (-19)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-8)) (.leaf (-9)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 20 (.leaf (0)) (.leaf (-10))),
  (.branch 5 (.leaf (0)) (.leaf (-25)))]
  high := ![(.branch 56 (.branch 48 (.leaf (-19)) (.branch 55 (.leaf (-18)) (.leaf (-15)))) (.branch 58 (.branch 57 (.leaf (-12)) (.leaf (-9))) (.branch 59 (.leaf (-6)) (.leaf (-3))))),
  (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 57 (.branch 43 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.branch 41 (.branch 38 (.branch 36 (.leaf (-25)) (.branch 37 (.leaf (-24)) (.leaf (-23)))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))) (.branch 44 (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17)))) (.branch 45 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_301_5478 : CycleWitness 9 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (8)) (.leaf (3))) (.branch 6 (.leaf (7)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (6)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (8)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (7)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (6)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (5)) (.leaf (2))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (8)) (.leaf (4))) (.branch 35 (.leaf (3)) (.leaf (0))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (7)) (.leaf (0))) (.branch 39 (.leaf (2)) (.leaf (6)))) (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (5)) (.leaf (0)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (8)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (2))) (.branch 50 (.leaf (0)) (.leaf (1))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (7)) (.leaf (3))) (.branch 54 (.leaf (0)) (.leaf (6)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_5478
  counts := ![(.branch 26 (.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 42 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 36 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 48 (.leaf (16)) (.leaf (17)))) (.branch 54 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 21 (.branch 2 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-47)) (.leaf (-51)))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 35 (.branch 5 (.leaf (0)) (.leaf (-17))) (.branch 45 (.leaf (-23)) (.branch 53 (.leaf (-25)) (.leaf (-33))))),
  (.branch 10 (.leaf (0)) (.branch 57 (.leaf (-2)) (.leaf (-3)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-6)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (-15)) (.leaf (-18)))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-11)) (.leaf (-13))))]
  high := ![(.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2)))),
  (.branch 53 (.branch 32 (.branch 22 (.leaf (-51)) (.leaf (-50))) (.branch 42 (.leaf (-49)) (.branch 52 (.leaf (-48)) (.leaf (-42))))) (.branch 56 (.branch 54 (.leaf (-36)) (.branch 55 (.leaf (-30)) (.leaf (-24)))) (.branch 57 (.leaf (-18)) (.branch 58 (.leaf (-12)) (.leaf (-6)))))),
  (.branch 9 (.leaf (-2)) (.branch 50 (.leaf (-1)) (.leaf (0)))),
  (.branch 56 (.branch 54 (.leaf (-33)) (.branch 55 (.leaf (-30)) (.leaf (-27)))) (.branch 57 (.leaf (-24)) (.branch 58 (.leaf (-21)) (.leaf (-18))))),
  (.branch 58 (.leaf (-3)) (.leaf (-2))),
  (.branch 29 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))),
  (.branch 56 (.branch 26 (.leaf (-18)) (.branch 41 (.leaf (-17)) (.leaf (-16)))) (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-8)) (.leaf (-4))))),
  (.branch 55 (.branch 53 (.branch 7 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.leaf (-2))))),
  (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2))))))]
def witnessP9_301_5479 : CycleWitness 9 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (6)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (5)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (3)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (4))) (.branch 28 (.leaf (0)) (.leaf (1))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (7)) (.branch 31 (.leaf (0)) (.leaf (2)))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (0))) (.branch 35 (.leaf (3)) (.leaf (0))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (1)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (5)))) (.branch 42 (.branch 41 (.leaf (1)) (.leaf (4))) (.branch 43 (.leaf (0)) (.leaf (3)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (1)) (.branch 46 (.leaf (0)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (8)) (.leaf (0))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (2)) (.leaf (1))) (.branch 54 (.leaf (3)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (4)) (.leaf (1))) (.branch 58 (.leaf (0)) (.leaf (5))))))))
  code := certificateP9_5479
  counts := ![(.branch 28 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 36 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 51 (.branch 46 (.leaf (15)) (.branch 48 (.leaf (16)) (.leaf (17)))) (.branch 55 (.leaf (18)) (.branch 58 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.leaf (15)))))),
  (.branch 23 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 24 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-6)) (.leaf (-10)))) (.branch 38 (.leaf (-13)) (.branch 52 (.leaf (-16)) (.leaf (-20))))),
  (.branch 5 (.leaf (0)) (.branch 44 (.leaf (-29)) (.leaf (-31)))),
  (.branch 12 (.leaf (0)) (.branch 56 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-50))),
  (.branch 30 (.leaf (0)) (.leaf (-29))),
  (.branch 50 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 52 (.leaf (-3)) (.leaf (-2))),
  (.branch 58 (.leaf (-3)) (.leaf (-2))),
  (.branch 55 (.branch 53 (.leaf (-20)) (.branch 54 (.leaf (-19)) (.leaf (-18)))) (.branch 57 (.branch 56 (.leaf (-17)) (.leaf (-16))) (.branch 58 (.leaf (-15)) (.leaf (-14))))),
  (.branch 56 (.branch 45 (.leaf (-31)) (.branch 55 (.leaf (-30)) (.leaf (-24)))) (.branch 57 (.leaf (-18)) (.branch 58 (.leaf (-12)) (.leaf (-6))))),
  (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 34 (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-50)) (.branch 11 (.leaf (-49)) (.leaf (-48)))) (.branch 13 (.leaf (-47)) (.branch 14 (.leaf (-46)) (.leaf (-45))))) (.branch 18 (.branch 16 (.leaf (-44)) (.branch 17 (.leaf (-43)) (.leaf (-42)))) (.branch 19 (.leaf (-41)) (.branch 20 (.leaf (-40)) (.leaf (-39)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-38)) (.branch 23 (.leaf (-37)) (.leaf (-36)))) (.branch 25 (.leaf (-35)) (.branch 26 (.leaf (-34)) (.leaf (-33))))) (.branch 30 (.branch 28 (.leaf (-32)) (.branch 29 (.leaf (-31)) (.leaf (-30)))) (.branch 32 (.branch 31 (.leaf (-29)) (.leaf (-28))) (.branch 33 (.leaf (-27)) (.leaf (-26))))))) (.branch 46 (.branch 40 (.branch 37 (.branch 35 (.leaf (-25)) (.branch 36 (.leaf (-24)) (.leaf (-23)))) (.branch 38 (.leaf (-22)) (.branch 39 (.leaf (-21)) (.leaf (-20))))) (.branch 43 (.branch 41 (.leaf (-19)) (.branch 42 (.leaf (-18)) (.leaf (-17)))) (.branch 44 (.leaf (-16)) (.branch 45 (.leaf (-15)) (.leaf (-14)))))) (.branch 52 (.branch 49 (.branch 47 (.leaf (-13)) (.branch 48 (.leaf (-12)) (.leaf (-11)))) (.branch 50 (.leaf (-10)) (.branch 51 (.leaf (-9)) (.leaf (-8))))) (.branch 55 (.branch 53 (.leaf (-7)) (.branch 54 (.leaf (-6)) (.leaf (-5)))) (.branch 57 (.branch 56 (.leaf (-4)) (.leaf (-3))) (.branch 58 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 44 (.branch 37 (.branch 33 (.branch 31 (.leaf (-29)) (.branch 32 (.leaf (-28)) (.leaf (-27)))) (.branch 35 (.branch 34 (.leaf (-26)) (.leaf (-25))) (.branch 36 (.leaf (-24)) (.leaf (-23))))) (.branch 40 (.branch 38 (.leaf (-22)) (.branch 39 (.leaf (-21)) (.leaf (-20)))) (.branch 42 (.branch 41 (.leaf (-19)) (.leaf (-18))) (.branch 43 (.leaf (-17)) (.leaf (-16)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (-15)) (.branch 46 (.leaf (-14)) (.leaf (-13)))) (.branch 49 (.branch 48 (.leaf (-12)) (.leaf (-11))) (.branch 50 (.leaf (-10)) (.leaf (-9))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-8)) (.leaf (-7))) (.branch 54 (.leaf (-6)) (.leaf (-5)))) (.branch 57 (.branch 56 (.leaf (-4)) (.leaf (-3))) (.branch 58 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 52 (.branch 51 (.leaf (-9)) (.leaf (-8))) (.branch 53 (.leaf (-7)) (.leaf (-6)))) (.branch 56 (.branch 55 (.leaf (-5)) (.leaf (-4))) (.branch 57 (.leaf (-3)) (.branch 58 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_301_5480 : CycleWitness 9 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (5)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (8)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (6)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (3)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (1)) (.leaf (7))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (4)) (.branch 31 (.leaf (0)) (.leaf (1)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (3))) (.branch 35 (.leaf (0)) (.leaf (5))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (6)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (4)))) (.branch 42 (.branch 41 (.leaf (2)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (3)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (8)) (.branch 46 (.leaf (1)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (4)) (.leaf (2))) (.branch 50 (.leaf (5)) (.leaf (1))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (6))) (.branch 54 (.leaf (3)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (2)) (.leaf (1))) (.branch 58 (.leaf (4)) (.leaf (7))))))))
  code := certificateP9_5480
  counts := ![(.branch 27 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.leaf (15)))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.leaf (0)) (.branch 59 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 46 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.branch 34 (.leaf (-29)) (.leaf (-32)))),
  (.branch 48 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.branch 50 (.leaf (-35)) (.leaf (-36)))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 29 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.leaf (-2)))),
  (.branch 52 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2)))),
  (.branch 57 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.leaf (-4)))),
  (.branch 55 (.branch 35 (.leaf (-32)) (.branch 45 (.leaf (-31)) (.leaf (-30)))) (.branch 57 (.branch 56 (.leaf (-24)) (.leaf (-18))) (.branch 58 (.leaf (-12)) (.leaf (-6))))),
  (.leaf (-2)),
  (.branch 54 (.branch 52 (.branch 51 (.leaf (-36)) (.leaf (-32))) (.branch 53 (.leaf (-28)) (.leaf (-24)))) (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-16))) (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 55 (.branch 38 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.leaf (-2))))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 51 (.branch 47 (.branch 15 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.leaf (-2))))))]
def witnessP9_301_5481 : CycleWitness 9 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (8)) (.branch 16 (.leaf (0)) (.leaf (6)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (2))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (5))) (.branch 28 (.leaf (0)) (.leaf (7))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (2)))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (0))) (.branch 35 (.leaf (4)) (.leaf (0))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (6)) (.leaf (1))) (.branch 39 (.leaf (3)) (.leaf (0)))) (.branch 42 (.branch 41 (.leaf (1)) (.leaf (2))) (.branch 43 (.leaf (0)) (.leaf (8)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (1)) (.branch 46 (.leaf (0)) (.leaf (5)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (4)) (.leaf (0))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (2)) (.leaf (1))) (.branch 54 (.leaf (3)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (6)) (.leaf (1))) (.branch 58 (.leaf (0)) (.leaf (7))))))))
  code := certificateP9_5481
  counts := ![(.branch 28 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 36 (.leaf (12)) (.branch 40 (.leaf (13)) (.leaf (14))))) (.branch 51 (.branch 46 (.leaf (15)) (.branch 48 (.leaf (16)) (.leaf (17)))) (.branch 55 (.leaf (18)) (.branch 58 (.leaf (19)) (.leaf (20))))))),
  (.branch 30 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 38 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.leaf (15)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.leaf (0)) (.branch 59 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 36 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 33 (.leaf (-2)) (.leaf (-3)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 21 (.leaf (-8)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.leaf (-23))),
  (.branch 5 (.leaf (0)) (.leaf (-39))),
  (.branch 7 (.leaf (0)) (.leaf (-38))),
  (.branch 17 (.leaf (0)) (.branch 56 (.leaf (-8)) (.leaf (-9)))),
  (.branch 29 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.branch 44 (.leaf (-29)) (.leaf (-30))))]
  high := ![(.branch 52 (.leaf (-3)) (.leaf (-2))),
  (.branch 58 (.leaf (-3)) (.leaf (-2))),
  (.branch 55 (.branch 53 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.leaf (-2))))),
  (.branch 55 (.branch 25 (.branch 10 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.leaf (-20)))) (.branch 57 (.branch 56 (.leaf (-16)) (.leaf (-12))) (.branch 58 (.leaf (-8)) (.leaf (-4))))),
  (.branch 53 (.branch 36 (.branch 6 (.leaf (-39)) (.branch 21 (.leaf (-38)) (.leaf (-37)))) (.branch 51 (.leaf (-36)) (.branch 52 (.leaf (-32)) (.leaf (-28))))) (.branch 56 (.branch 54 (.leaf (-24)) (.branch 55 (.leaf (-20)) (.leaf (-16)))) (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 52 (.branch 48 (.branch 8 (.leaf (-38)) (.branch 28 (.leaf (-37)) (.leaf (-36)))) (.branch 50 (.branch 49 (.leaf (-33)) (.leaf (-30))) (.branch 51 (.leaf (-27)) (.leaf (-24))))) (.branch 55 (.branch 53 (.leaf (-21)) (.branch 54 (.leaf (-18)) (.leaf (-15)))) (.branch 57 (.branch 56 (.leaf (-12)) (.leaf (-9))) (.branch 58 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 57 (.leaf (-9)) (.branch 58 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 51 (.branch 47 (.branch 45 (.leaf (-30)) (.branch 46 (.leaf (-28)) (.leaf (-26)))) (.branch 49 (.branch 48 (.leaf (-24)) (.leaf (-22))) (.branch 50 (.leaf (-20)) (.leaf (-18))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-16)) (.leaf (-14))) (.branch 54 (.leaf (-12)) (.leaf (-10)))) (.branch 57 (.branch 56 (.leaf (-8)) (.leaf (-6))) (.branch 58 (.leaf (-4)) (.leaf (-2))))))]
def witnessP9_301_5482 : CycleWitness 9 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (1)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (7)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (6)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (8))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (3)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (0))) (.branch 35 (.leaf (4)) (.leaf (1))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (6)) (.leaf (0))) (.branch 39 (.leaf (5)) (.leaf (2)))) (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (3)) (.leaf (7)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (4)))) (.branch 49 (.branch 48 (.leaf (2)) (.leaf (0))) (.branch 50 (.leaf (6)) (.leaf (1))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (5)) (.leaf (0))) (.branch 54 (.leaf (2)) (.leaf (3)))) (.branch 57 (.branch 56 (.leaf (1)) (.leaf (0))) (.branch 58 (.leaf (8)) (.leaf (4))))))))
  code := certificateP9_5482
  counts := ![(.branch 27 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 12 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 29 (.leaf (0)) (.branch 58 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))) (.branch 30 (.leaf (-5)) (.branch 45 (.leaf (-6)) (.leaf (-7))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-35)) (.leaf (-46)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-31))) (.branch 54 (.leaf (-34)) (.leaf (-38)))),
  (.branch 8 (.leaf (0)) (.branch 43 (.leaf (-19)) (.leaf (-21)))),
  (.branch 23 (.leaf (0)) (.leaf (-3))),
  (.branch 28 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 39 (.leaf (-8)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.branch 50 (.leaf (-8)) (.leaf (-10)))),
  (.branch 14 (.leaf (0)) (.leaf (-31))),
  (.branch 29 (.leaf (0)) (.branch 58 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 58 (.leaf (-7)) (.leaf (-6))),
  (.branch 32 (.branch 17 (.branch 7 (.leaf (-46)) (.branch 12 (.leaf (-45)) (.leaf (-44)))) (.branch 22 (.leaf (-43)) (.branch 27 (.leaf (-42)) (.leaf (-41))))) (.branch 47 (.branch 37 (.leaf (-40)) (.branch 42 (.leaf (-39)) (.leaf (-38)))) (.branch 57 (.branch 52 (.leaf (-37)) (.leaf (-36))) (.branch 58 (.leaf (-24)) (.leaf (-12)))))),
  (.branch 56 (.branch 55 (.leaf (-38)) (.leaf (-31))) (.branch 57 (.leaf (-24)) (.branch 58 (.leaf (-17)) (.leaf (-10))))),
  (.branch 56 (.branch 44 (.leaf (-21)) (.leaf (-20))) (.branch 57 (.leaf (-15)) (.branch 58 (.leaf (-10)) (.leaf (-5))))),
  (.branch 36 (.branch 24 (.leaf (-3)) (.leaf (-2))) (.branch 48 (.leaf (-1)) (.leaf (0)))),
  (.branch 55 (.branch 53 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.leaf (-2))))),
  (.branch 54 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.leaf (-7)))) (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 15 (.leaf (-31)) (.leaf (-30))) (.branch 46 (.leaf (-28)) (.leaf (-26)))) (.branch 49 (.branch 48 (.leaf (-24)) (.leaf (-22))) (.branch 50 (.leaf (-20)) (.leaf (-18))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-16)) (.leaf (-14))) (.branch 54 (.leaf (-12)) (.leaf (-10)))) (.branch 57 (.branch 56 (.leaf (-8)) (.leaf (-6))) (.branch 58 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (-2))]
def witnessP9_301_5483 : CycleWitness 9 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (7)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (5)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (8)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (3))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (6)) (.leaf (2))) (.branch 24 (.leaf (5)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (3))) (.branch 28 (.leaf (7)) (.leaf (2))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (4)) (.branch 31 (.leaf (0)) (.leaf (1)))) (.branch 34 (.branch 33 (.leaf (3)) (.leaf (5))) (.branch 35 (.leaf (0)) (.leaf (2))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (6)) (.leaf (1))) (.branch 39 (.leaf (8)) (.leaf (3)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (4))) (.branch 43 (.leaf (2)) (.leaf (1)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (5)) (.leaf (7)))) (.branch 49 (.branch 48 (.leaf (3)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (0))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (6)) (.leaf (4))) (.branch 54 (.leaf (0)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (3)) (.leaf (2))) (.branch 58 (.leaf (8)) (.leaf (5))))))))
  code := certificateP9_5483
  counts := ![(.branch 25 (.branch 11 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 50 (.leaf (7)) (.branch 57 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 13 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 54 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 49 (.leaf (-39)) (.leaf (-41)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-15))) (.branch 29 (.leaf (-18)) (.leaf (-19)))),
  (.branch 33 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 40 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.branch 53 (.leaf (-29)) (.leaf (-30)))),
  (.branch 34 (.branch 24 (.leaf (0)) (.leaf (-2))) (.branch 46 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 28 (.branch 10 (.leaf (0)) (.leaf (-11))) (.branch 47 (.leaf (-14)) (.leaf (-16)))),
  (.branch 17 (.leaf (0)) (.branch 58 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2))))),
  (.branch 56 (.branch 50 (.leaf (-41)) (.leaf (-40))) (.branch 57 (.leaf (-30)) (.branch 58 (.leaf (-20)) (.leaf (-10))))),
  (.branch 44 (.branch 30 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17)))) (.branch 51 (.leaf (-16)) (.branch 58 (.leaf (-15)) (.leaf (-11))))),
  (.branch 49 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-6)) (.leaf (-4))))),
  (.branch 56 (.branch 54 (.leaf (-30)) (.branch 55 (.leaf (-25)) (.leaf (-20)))) (.branch 57 (.leaf (-15)) (.branch 58 (.leaf (-10)) (.leaf (-5))))),
  (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-6))) (.branch 49 (.leaf (-4)) (.branch 50 (.leaf (-2)) (.leaf (0))))),
  (.branch 54 (.branch 23 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 38 (.leaf (-29)) (.branch 53 (.leaf (-28)) (.leaf (-24))))) (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-16))) (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 53 (.branch 50 (.branch 48 (.leaf (-16)) (.branch 49 (.leaf (-15)) (.leaf (-14)))) (.branch 51 (.leaf (-13)) (.branch 52 (.leaf (-12)) (.leaf (-11))))) (.branch 56 (.branch 54 (.leaf (-10)) (.branch 55 (.leaf (-9)) (.leaf (-8)))) (.branch 57 (.leaf (-7)) (.branch 58 (.leaf (-6)) (.leaf (-5)))))),
  (.leaf (-5))]
def witnessP9_301_5484 : CycleWitness 9 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (6))) (.branch 6 (.leaf (8)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (2))) (.branch 13 (.leaf (7)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (6)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (8))) (.branch 20 (.leaf (1)) (.leaf (2))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (3)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (7)) (.leaf (1))) (.branch 28 (.leaf (4)) (.leaf (6))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (1)))) (.branch 34 (.branch 33 (.leaf (3)) (.leaf (8))) (.branch 35 (.leaf (5)) (.leaf (0))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (2)) (.leaf (4))) (.branch 39 (.leaf (1)) (.leaf (0)))) (.branch 42 (.branch 41 (.leaf (6)) (.leaf (7))) (.branch 43 (.leaf (3)) (.leaf (1)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (2)) (.branch 46 (.leaf (0)) (.leaf (5)))) (.branch 49 (.branch 48 (.leaf (4)) (.leaf (8))) (.branch 50 (.leaf (1)) (.leaf (0))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (6)) (.leaf (3))) (.branch 54 (.leaf (2)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (1)) (.leaf (7))) (.branch 58 (.leaf (5)) (.leaf (4))))))))
  code := certificateP9_5484
  counts := ![(.branch 25 (.branch 10 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 25 (.branch 1 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-13)))) (.branch 40 (.leaf (-16)) (.branch 55 (.leaf (-19)) (.leaf (-22))))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 37 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 45 (.leaf (-19)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.branch 33 (.leaf (-35)) (.leaf (-38)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 11 (.leaf (0)) (.branch 58 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 52 (.leaf (-34)) (.leaf (-35)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-2)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-9)) (.leaf (-11))))]
  high := ![(.branch 57 (.branch 56 (.leaf (-22)) (.leaf (-20))) (.branch 58 (.leaf (-18)) (.leaf (-16)))),
  (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2)))),
  (.branch 56 (.branch 46 (.leaf (-21)) (.branch 55 (.leaf (-20)) (.leaf (-17)))) (.branch 57 (.leaf (-14)) (.branch 58 (.leaf (-11)) (.leaf (-8))))),
  (.branch 55 (.branch 44 (.branch 34 (.leaf (-38)) (.leaf (-37))) (.branch 54 (.leaf (-36)) (.leaf (-30)))) (.branch 57 (.branch 56 (.leaf (-24)) (.leaf (-18))) (.branch 58 (.leaf (-12)) (.leaf (-6))))),
  (.branch 49 (.leaf (-2)) (.branch 50 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-5)),
  (.branch 55 (.branch 53 (.leaf (-35)) (.branch 54 (.leaf (-30)) (.leaf (-25)))) (.branch 57 (.branch 56 (.leaf (-20)) (.leaf (-15))) (.branch 58 (.leaf (-10)) (.leaf (-5))))),
  (.branch 27 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2)))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2))))))]
def witnessP9_301_5485 : CycleWitness 9 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (7)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (8)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (4))) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (1))) (.branch 24 (.leaf (5)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (7))) (.branch 28 (.leaf (0)) (.leaf (2))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (4)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (6)) (.leaf (1))) (.branch 35 (.leaf (3)) (.leaf (0))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (2)) (.leaf (8))) (.branch 39 (.leaf (1)) (.leaf (0)))) (.branch 42 (.branch 41 (.leaf (4)) (.leaf (1))) (.branch 43 (.leaf (5)) (.leaf (0)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (7))) (.branch 50 (.leaf (1)) (.leaf (4))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (6))) (.branch 54 (.leaf (2)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (3))) (.branch 58 (.leaf (1)) (.leaf (8))))))))
  code := certificateP9_5485
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.leaf (15)))))),
  (.branch 31 (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 39 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 55 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.leaf (15)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 28 (.leaf (-44)) (.leaf (-52)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 45 (.leaf (-38)) (.leaf (-39)))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (-1))) (.branch 57 (.leaf (-2)) (.leaf (-3)))),
  (.branch 30 (.branch 6 (.leaf (0)) (.leaf (-7))) (.branch 41 (.leaf (-9)) (.branch 51 (.leaf (-11)) (.leaf (-14))))),
  (.branch 4 (.leaf (0)) (.branch 43 (.leaf (-47)) (.leaf (-48)))),
  (.branch 14 (.leaf (0)) (.branch 33 (.leaf (-17)) (.leaf (-19)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-13)) (.leaf (-15)))),
  (.branch 16 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 45 (.branch 33 (.branch 29 (.leaf (-52)) (.leaf (-51))) (.branch 37 (.leaf (-50)) (.branch 41 (.leaf (-49)) (.leaf (-48))))) (.branch 53 (.branch 49 (.leaf (-47)) (.leaf (-46))) (.branch 57 (.leaf (-45)) (.branch 58 (.leaf (-30)) (.leaf (-15)))))),
  (.leaf (-2)),
  (.branch 56 (.branch 46 (.leaf (-39)) (.branch 55 (.leaf (-35)) (.leaf (-28)))) (.branch 57 (.leaf (-21)) (.branch 58 (.leaf (-14)) (.leaf (-7))))),
  (.branch 58 (.leaf (-3)) (.leaf (-2))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-14)) (.leaf (-13))) (.branch 54 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-9))) (.branch 58 (.leaf (-8)) (.leaf (-7))))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-48)) (.leaf (-45))) (.branch 46 (.leaf (-42)) (.leaf (-39)))) (.branch 49 (.branch 48 (.leaf (-36)) (.leaf (-33))) (.branch 50 (.leaf (-30)) (.leaf (-27))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-24)) (.leaf (-21))) (.branch 54 (.leaf (-18)) (.leaf (-15)))) (.branch 57 (.branch 56 (.leaf (-12)) (.leaf (-9))) (.branch 58 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 55 (.branch 34 (.leaf (-19)) (.branch 54 (.leaf (-18)) (.leaf (-15)))) (.branch 57 (.branch 56 (.leaf (-12)) (.leaf (-9))) (.branch 58 (.leaf (-6)) (.leaf (-3))))),
  (.branch 53 (.branch 50 (.branch 28 (.leaf (-15)) (.leaf (-14))) (.branch 51 (.leaf (-13)) (.branch 52 (.leaf (-12)) (.leaf (-11))))) (.branch 56 (.branch 54 (.leaf (-10)) (.branch 55 (.leaf (-9)) (.leaf (-8)))) (.branch 57 (.leaf (-7)) (.branch 58 (.leaf (-6)) (.leaf (-5)))))),
  (.branch 40 (.branch 17 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3)))) (.branch 41 (.leaf (-2)) (.branch 42 (.leaf (-1)) (.leaf (0)))))]
def witnessP9_301_5486 : CycleWitness 9 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (5))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (6)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (8)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (6)) (.leaf (3))) (.branch 24 (.leaf (7)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (4))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (3)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (8))) (.branch 35 (.leaf (6)) (.leaf (0))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (1)) (.leaf (4))) (.branch 39 (.leaf (2)) (.leaf (5)))) (.branch 42 (.branch 41 (.leaf (3)) (.leaf (0))) (.branch 43 (.leaf (1)) (.leaf (7)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (2)) (.leaf (6)))) (.branch 49 (.branch 48 (.leaf (4)) (.leaf (1))) (.branch 50 (.leaf (3)) (.leaf (0))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (5)) (.leaf (8))) (.branch 54 (.leaf (2)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (3))) (.branch 58 (.leaf (4)) (.leaf (6))))))))
  code := certificateP9_5486
  counts := ![(.branch 27 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 30 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.leaf (7))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 21 (.branch 1 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-12)))) (.branch 30 (.leaf (-13)) (.branch 45 (.leaf (-17)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-39)) (.leaf (-47)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-23))) (.branch 39 (.leaf (-26)) (.branch 46 (.leaf (-33)) (.leaf (-36))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (-8))) (.branch 57 (.leaf (-9)) (.leaf (-11)))),
  (.branch 9 (.leaf (0)) (.branch 38 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-34)) (.leaf (-37)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-47))),
  (.branch 14 (.leaf (0)) (.branch 53 (.leaf (-17)) (.leaf (-18))))]
  high := ![(.branch 57 (.leaf (-20)) (.branch 58 (.leaf (-18)) (.leaf (-16)))),
  (.branch 38 (.branch 20 (.branch 14 (.leaf (-47)) (.leaf (-46))) (.branch 26 (.leaf (-45)) (.branch 32 (.leaf (-44)) (.leaf (-43))))) (.branch 56 (.branch 44 (.leaf (-42)) (.branch 50 (.leaf (-41)) (.leaf (-40)))) (.branch 57 (.leaf (-30)) (.branch 58 (.leaf (-20)) (.leaf (-10)))))),
  (.branch 56 (.branch 47 (.leaf (-36)) (.branch 55 (.leaf (-34)) (.leaf (-29)))) (.branch 57 (.leaf (-24)) (.branch 58 (.leaf (-19)) (.leaf (-14))))),
  (.branch 58 (.leaf (-11)) (.leaf (-8))),
  (.leaf (-2)),
  (.branch 54 (.branch 41 (.branch 29 (.leaf (-37)) (.leaf (-36))) (.branch 53 (.leaf (-35)) (.leaf (-30)))) (.branch 56 (.branch 55 (.leaf (-25)) (.leaf (-20))) (.branch 57 (.leaf (-15)) (.branch 58 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 23 (.leaf (-2)) (.branch 48 (.leaf (-1)) (.leaf (0)))),
  (.branch 50 (.branch 46 (.branch 25 (.branch 5 (.leaf (-47)) (.leaf (-46))) (.branch 45 (.leaf (-45)) (.leaf (-42)))) (.branch 48 (.branch 47 (.leaf (-39)) (.leaf (-36))) (.branch 49 (.leaf (-33)) (.leaf (-30))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-27)) (.leaf (-24))) (.branch 53 (.leaf (-21)) (.leaf (-18)))) (.branch 56 (.branch 55 (.leaf (-15)) (.leaf (-12))) (.branch 57 (.leaf (-9)) (.branch 58 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 56 (.branch 54 (.leaf (-18)) (.branch 55 (.leaf (-15)) (.leaf (-12)))) (.branch 57 (.leaf (-9)) (.branch 58 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_301_5487 : CycleWitness 9 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (7)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (8)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (6))) (.branch 20 (.leaf (7)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (2))) (.branch 24 (.leaf (5)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (4))) (.branch 28 (.leaf (8)) (.leaf (0))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (6)) (.branch 31 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (7)) (.leaf (5))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (2)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (3))) (.branch 43 (.leaf (6)) (.leaf (8)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (5)))) (.branch 49 (.branch 48 (.leaf (2)) (.leaf (0))) (.branch 50 (.leaf (7)) (.leaf (4))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (3)) (.leaf (0))) (.branch 54 (.leaf (1)) (.leaf (6)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (2))) (.branch 58 (.leaf (5)) (.leaf (8))))))))
  code := certificateP9_5487
  counts := ![(.branch 29 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.leaf (15)))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 56 (.leaf (-44)) (.leaf (-45)))),
  (.branch 2 (.leaf (0)) (.branch 38 (.leaf (-23)) (.leaf (-34)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-41)) (.leaf (-46)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-39)) (.leaf (-43)))),
  (.branch 11 (.leaf (0)) (.branch 58 (.leaf (-1)) (.leaf (-2)))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (-4))) (.branch 30 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (-35)) (.leaf (-38)))),
  (.branch 28 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 57 (.leaf (-45)) (.branch 58 (.leaf (-30)) (.leaf (-15)))),
  (.branch 55 (.branch 39 (.leaf (-34)) (.branch 47 (.leaf (-33)) (.leaf (-32)))) (.branch 57 (.branch 56 (.leaf (-28)) (.leaf (-24))) (.branch 58 (.leaf (-20)) (.leaf (-16))))),
  (.branch 49 (.leaf (-6)) (.branch 58 (.leaf (-5)) (.leaf (-3)))),
  (.branch 53 (.branch 23 (.branch 13 (.leaf (-46)) (.leaf (-45))) (.branch 33 (.leaf (-44)) (.branch 43 (.leaf (-43)) (.leaf (-42))))) (.branch 56 (.branch 54 (.leaf (-36)) (.branch 55 (.leaf (-30)) (.leaf (-24)))) (.branch 57 (.leaf (-18)) (.branch 58 (.leaf (-12)) (.leaf (-6)))))),
  (.branch 53 (.branch 28 (.branch 16 (.leaf (-43)) (.leaf (-42))) (.branch 40 (.leaf (-41)) (.branch 52 (.leaf (-40)) (.leaf (-35))))) (.branch 56 (.branch 54 (.leaf (-30)) (.branch 55 (.leaf (-25)) (.leaf (-20)))) (.branch 57 (.leaf (-15)) (.branch 58 (.leaf (-10)) (.leaf (-5)))))),
  (.leaf (-2)),
  (.branch 56 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2))))),
  (.branch 53 (.branch 36 (.branch 21 (.leaf (-38)) (.leaf (-37))) (.branch 51 (.leaf (-36)) (.branch 52 (.leaf (-32)) (.leaf (-28))))) (.branch 56 (.branch 54 (.leaf (-24)) (.branch 55 (.leaf (-20)) (.leaf (-16)))) (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 45 (.branch 29 (.leaf (-8)) (.leaf (-6))) (.branch 46 (.leaf (-3)) (.leaf (0))))]
def witnessP9_301_5488 : CycleWitness 9 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (4))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (8)) (.leaf (6)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (7))) (.branch 20 (.leaf (1)) (.leaf (3))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (4)) (.leaf (6)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (8))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (1)))) (.branch 34 (.branch 33 (.leaf (5)) (.leaf (4))) (.branch 35 (.leaf (2)) (.leaf (3))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (7)) (.leaf (6)))) (.branch 42 (.branch 41 (.leaf (2)) (.leaf (0))) (.branch 43 (.leaf (1)) (.leaf (4)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (3)) (.branch 46 (.leaf (0)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (5)) (.leaf (1))) (.branch 50 (.leaf (8)) (.leaf (0))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (2)) (.leaf (3))) (.branch 54 (.leaf (4)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (6)) (.leaf (0))) (.branch 58 (.leaf (2)) (.leaf (7))))))))
  code := certificateP9_5488
  counts := ![(.branch 27 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 31 (.branch 1 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-12)))) (.branch 46 (.leaf (-15)) (.branch 51 (.leaf (-18)) (.leaf (-19))))),
  (.branch 2 (.leaf (0)) (.branch 43 (.leaf (-39)) (.leaf (-42)))),
  (.branch 11 (.leaf (0)) (.branch 52 (.leaf (-1)) (.leaf (-2)))),
  (.branch 28 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 36 (.leaf (-20)) (.branch 53 (.leaf (-22)) (.leaf (-23))))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-29)) (.leaf (-33)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-11)) (.leaf (-13)))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 19 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 52 (.leaf (-19)) (.branch 58 (.leaf (-18)) (.leaf (-16)))),
  (.branch 56 (.branch 44 (.leaf (-42)) (.branch 50 (.leaf (-41)) (.leaf (-40)))) (.branch 57 (.leaf (-30)) (.branch 58 (.leaf (-20)) (.leaf (-10))))),
  (.leaf (-2)),
  (.branch 56 (.branch 54 (.leaf (-23)) (.branch 55 (.leaf (-20)) (.leaf (-17)))) (.branch 57 (.leaf (-14)) (.branch 58 (.leaf (-11)) (.leaf (-8))))),
  (.branch 55 (.branch 35 (.branch 25 (.leaf (-33)) (.leaf (-32))) (.branch 45 (.leaf (-31)) (.leaf (-30)))) (.branch 57 (.branch 56 (.leaf (-24)) (.leaf (-18))) (.branch 58 (.leaf (-12)) (.leaf (-6))))),
  (.branch 53 (.branch 50 (.branch 18 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 57 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.leaf (-2)))),
  (.branch 20 (.leaf (-2)) (.branch 40 (.leaf (-1)) (.leaf (0)))),
  (.branch 54 (.branch 51 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2))))))]
def witnessP9_301_5489 : CycleWitness 9 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (7))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (6)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (8)) (.branch 16 (.leaf (0)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (4))) (.branch 20 (.leaf (1)) (.leaf (3))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (7)) (.leaf (6)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (4))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (1)))) (.branch 34 (.branch 33 (.leaf (5)) (.leaf (8))) (.branch 35 (.leaf (2)) (.leaf (3))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (6)))) (.branch 42 (.branch 41 (.leaf (2)) (.leaf (0))) (.branch 43 (.leaf (1)) (.leaf (7)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (3)) (.branch 46 (.leaf (0)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (5)) (.leaf (1))) (.branch 50 (.leaf (4)) (.leaf (0))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (2)) (.leaf (3))) (.branch 54 (.leaf (8)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (6)) (.leaf (0))) (.branch 58 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_5489
  counts := ![(.branch 27 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.leaf (7))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 31 (.branch 1 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-12)))) (.branch 46 (.leaf (-15)) (.branch 51 (.leaf (-18)) (.leaf (-19))))),
  (.branch 2 (.leaf (0)) (.branch 43 (.leaf (-39)) (.leaf (-42)))),
  (.branch 11 (.leaf (0)) (.branch 52 (.leaf (-1)) (.leaf (-2)))),
  (.branch 28 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 36 (.leaf (-20)) (.branch 53 (.leaf (-22)) (.leaf (-23))))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-11)) (.leaf (-13)))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-44)) (.leaf (-46)))),
  (.branch 15 (.leaf (0)) (.branch 34 (.leaf (-14)) (.leaf (-16))))]
  high := ![(.branch 52 (.leaf (-19)) (.branch 58 (.leaf (-18)) (.leaf (-16)))),
  (.branch 56 (.branch 44 (.leaf (-42)) (.branch 50 (.leaf (-41)) (.leaf (-40)))) (.branch 57 (.leaf (-30)) (.branch 58 (.leaf (-20)) (.leaf (-10))))),
  (.leaf (-2)),
  (.branch 56 (.branch 54 (.leaf (-23)) (.branch 55 (.leaf (-20)) (.leaf (-17)))) (.branch 57 (.leaf (-14)) (.branch 58 (.leaf (-11)) (.leaf (-8))))),
  (.branch 40 (.leaf (-1)) (.leaf (0))),
  (.branch 53 (.branch 50 (.branch 18 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 57 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.leaf (-2)))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 25 (.leaf (-46)) (.leaf (-45))) (.branch 46 (.leaf (-42)) (.leaf (-39)))) (.branch 49 (.branch 48 (.leaf (-36)) (.leaf (-33))) (.branch 50 (.leaf (-30)) (.leaf (-27))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-24)) (.leaf (-21))) (.branch 54 (.leaf (-18)) (.leaf (-15)))) (.branch 57 (.branch 56 (.leaf (-12)) (.leaf (-9))) (.branch 58 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 56 (.branch 35 (.leaf (-16)) (.branch 55 (.leaf (-15)) (.leaf (-12)))) (.branch 57 (.leaf (-9)) (.branch 58 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_301_5490 : CycleWitness 9 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (4)) (.leaf (8))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (7)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (8)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (5)) (.leaf (0))) (.branch 28 (.leaf (1)) (.leaf (7))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (3)) (.branch 31 (.leaf (0)) (.leaf (1)))) (.branch 34 (.branch 33 (.leaf (6)) (.leaf (2))) (.branch 35 (.leaf (0)) (.leaf (4))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (8)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (3)))) (.branch 42 (.branch 41 (.leaf (5)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (2)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (7)) (.branch 46 (.leaf (1)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (3)) (.leaf (6))) (.branch 50 (.leaf (4)) (.leaf (1))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (8))) (.branch 54 (.leaf (2)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (5)) (.leaf (1))) (.branch 58 (.leaf (3)) (.leaf (7))))))))
  code := certificateP9_5490
  counts := ![(.branch 27 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.leaf (15)))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 46 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 34 (.leaf (-29)) (.leaf (-32)))),
  (.branch 48 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.branch 50 (.leaf (-35)) (.leaf (-36)))),
  (.branch 11 (.leaf (0)) (.leaf (-15))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.leaf (-2)))),
  (.branch 52 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2)))),
  (.branch 55 (.branch 35 (.leaf (-32)) (.branch 45 (.leaf (-31)) (.leaf (-30)))) (.branch 57 (.branch 56 (.leaf (-24)) (.leaf (-18))) (.branch 58 (.leaf (-12)) (.leaf (-6))))),
  (.leaf (-2)),
  (.branch 54 (.branch 52 (.branch 51 (.leaf (-36)) (.leaf (-32))) (.branch 53 (.leaf (-28)) (.leaf (-24)))) (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-16))) (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 42 (.branch 12 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-8)) (.leaf (-4))))),
  (.branch 53 (.branch 50 (.branch 34 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 55 (.branch 38 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.leaf (-2)))))]
def witnessP9_301_5491 : CycleWitness 9 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (7))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (5)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (8)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (1))) (.branch 20 (.leaf (5)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (3))) (.branch 24 (.leaf (4)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (7))) (.branch 28 (.leaf (1)) (.leaf (2))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (6)) (.branch 31 (.leaf (0)) (.leaf (3)))) (.branch 34 (.branch 33 (.leaf (5)) (.leaf (1))) (.branch 35 (.leaf (4)) (.leaf (0))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (2)) (.leaf (8))) (.branch 39 (.leaf (1)) (.leaf (6)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (3))) (.branch 43 (.leaf (1)) (.leaf (5)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (2)) (.branch 46 (.leaf (0)) (.leaf (4)))) (.branch 49 (.branch 48 (.leaf (7)) (.leaf (1))) (.branch 50 (.leaf (0)) (.leaf (6))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (3)) (.leaf (2))) (.branch 54 (.leaf (1)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (5)) (.leaf (8))) (.branch 58 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_5491
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 14 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 50 (.leaf (-47)) (.leaf (-49)))),
  (.branch 4 (.leaf (0)) (.branch 28 (.leaf (-1)) (.leaf (-2)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-23)) (.leaf (-30)))) (.branch 22 (.leaf (-33)) (.branch 29 (.leaf (-36)) (.leaf (-39))))),
  (.branch 3 (.leaf (0)) (.branch 32 (.leaf (-41)) (.leaf (-44)))),
  (.branch 35 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 40 (.branch 5 (.leaf (0)) (.leaf (-15))) (.branch 51 (.leaf (-20)) (.leaf (-23)))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 17 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 56 (.branch 51 (.leaf (-49)) (.leaf (-48))) (.branch 57 (.leaf (-36)) (.branch 58 (.leaf (-24)) (.leaf (-12))))),
  (.leaf (-2)),
  (.branch 54 (.branch 38 (.branch 30 (.leaf (-39)) (.leaf (-38))) (.branch 46 (.leaf (-37)) (.leaf (-36)))) (.branch 56 (.branch 55 (.leaf (-32)) (.leaf (-28))) (.branch 57 (.leaf (-24)) (.branch 58 (.leaf (-20)) (.leaf (-16)))))),
  (.branch 54 (.branch 43 (.branch 33 (.leaf (-44)) (.leaf (-43))) (.branch 53 (.leaf (-42)) (.leaf (-36)))) (.branch 56 (.branch 55 (.leaf (-30)) (.leaf (-24))) (.branch 57 (.leaf (-18)) (.branch 58 (.leaf (-12)) (.leaf (-6)))))),
  (.branch 36 (.leaf (-2)) (.branch 48 (.leaf (-1)) (.leaf (0)))),
  (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2)))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-23)) (.leaf (-21))) (.branch 54 (.leaf (-19)) (.leaf (-17)))) (.branch 57 (.branch 56 (.leaf (-15)) (.leaf (-13))) (.branch 58 (.leaf (-11)) (.leaf (-9))))),
  (.branch 53 (.branch 50 (.branch 28 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 58 (.leaf (-3)) (.leaf (-2)))]
def witnessP9_301_5492 : CycleWitness 9 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (8))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (7)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (6))) (.branch 20 (.leaf (4)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (3))) (.branch 24 (.leaf (1)) (.leaf (8)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (5))) (.branch 28 (.leaf (2)) (.leaf (1))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (4)) (.branch 31 (.leaf (0)) (.leaf (3)))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (2))) (.branch 35 (.leaf (6)) (.leaf (0))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (7)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (0)))) (.branch 42 (.branch 41 (.leaf (2)) (.leaf (3))) (.branch 43 (.leaf (5)) (.leaf (1)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (8)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (4))) (.branch 50 (.leaf (0)) (.leaf (6))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (3)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (7)) (.leaf (5))) (.branch 58 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_5492
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 40 (.leaf (-47)) (.leaf (-51)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-23))) (.branch 34 (.leaf (-26)) (.branch 47 (.leaf (-28)) (.leaf (-29))))),
  (.branch 3 (.leaf (0)) (.branch 32 (.leaf (-41)) (.leaf (-44)))),
  (.branch 39 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-21)) (.leaf (-24)))),
  (.branch 17 (.leaf (0)) (.branch 56 (.leaf (-8)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (-13)) (.leaf (-15))))]
  high := ![(.branch 51 (.branch 41 (.leaf (-51)) (.branch 46 (.leaf (-50)) (.leaf (-49)))) (.branch 57 (.branch 56 (.leaf (-48)) (.leaf (-36))) (.branch 58 (.leaf (-24)) (.leaf (-12))))),
  (.leaf (-2)),
  (.branch 56 (.branch 48 (.leaf (-29)) (.branch 55 (.leaf (-27)) (.leaf (-22)))) (.branch 57 (.leaf (-17)) (.branch 58 (.leaf (-12)) (.leaf (-7))))),
  (.branch 54 (.branch 43 (.branch 33 (.leaf (-44)) (.leaf (-43))) (.branch 53 (.leaf (-42)) (.leaf (-36)))) (.branch 56 (.branch 55 (.leaf (-30)) (.leaf (-24))) (.branch 57 (.leaf (-18)) (.branch 58 (.leaf (-12)) (.leaf (-6)))))),
  (.branch 40 (.leaf (-2)) (.branch 50 (.leaf (-1)) (.leaf (0)))),
  (.branch 58 (.leaf (-3)) (.leaf (-2))),
  (.branch 54 (.branch 36 (.branch 20 (.leaf (-24)) (.leaf (-23))) (.branch 52 (.leaf (-22)) (.branch 53 (.leaf (-20)) (.leaf (-18))))) (.branch 56 (.branch 55 (.leaf (-16)) (.leaf (-14))) (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-10)) (.leaf (-8)))))),
  (.branch 57 (.leaf (-9)) (.branch 58 (.leaf (-6)) (.leaf (-3)))),
  (.branch 52 (.branch 48 (.branch 26 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 55 (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.leaf (-2))))))]
def witnessP9_301_5493 : CycleWitness 9 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (8))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (6)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (7)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (3))) (.branch 20 (.leaf (4)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (5))) (.branch 24 (.leaf (1)) (.leaf (8)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (2)) (.leaf (1))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (4)) (.branch 31 (.leaf (0)) (.leaf (6)))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (2))) (.branch 35 (.leaf (3)) (.leaf (0))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (7)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (0)))) (.branch 42 (.branch 41 (.leaf (2)) (.leaf (5))) (.branch 43 (.leaf (3)) (.leaf (1)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (8)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (4))) (.branch 50 (.leaf (0)) (.leaf (3))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (6)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (7)) (.leaf (3))) (.branch 58 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_5493
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 40 (.leaf (-47)) (.leaf (-51)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-23))) (.branch 34 (.leaf (-26)) (.branch 47 (.leaf (-28)) (.leaf (-29))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-11))) (.branch 19 (.leaf (-14)) (.branch 57 (.leaf (-17)) (.leaf (-20))))),
  (.branch 39 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 42 (.leaf (-50)) (.leaf (-51)))),
  (.branch 13 (.leaf (0)) (.branch 32 (.leaf (-20)) (.leaf (-22)))),
  (.branch 17 (.leaf (0)) (.branch 56 (.leaf (-8)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (-13)) (.leaf (-15))))]
  high := ![(.branch 51 (.branch 41 (.leaf (-51)) (.branch 46 (.leaf (-50)) (.leaf (-49)))) (.branch 57 (.branch 56 (.leaf (-48)) (.leaf (-36))) (.branch 58 (.leaf (-24)) (.leaf (-12))))),
  (.leaf (-2)),
  (.branch 56 (.branch 48 (.leaf (-29)) (.branch 55 (.leaf (-27)) (.leaf (-22)))) (.branch 57 (.leaf (-17)) (.branch 58 (.leaf (-12)) (.leaf (-7))))),
  (.branch 58 (.leaf (-20)) (.leaf (-16))),
  (.branch 40 (.leaf (-2)) (.branch 50 (.leaf (-1)) (.leaf (0)))),
  (.branch 50 (.branch 46 (.branch 44 (.branch 43 (.leaf (-51)) (.leaf (-48))) (.branch 45 (.leaf (-45)) (.leaf (-42)))) (.branch 48 (.branch 47 (.leaf (-39)) (.leaf (-36))) (.branch 49 (.leaf (-33)) (.leaf (-30))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-27)) (.leaf (-24))) (.branch 53 (.leaf (-21)) (.leaf (-18)))) (.branch 56 (.branch 55 (.leaf (-15)) (.leaf (-12))) (.branch 57 (.leaf (-9)) (.branch 58 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 55 (.branch 53 (.branch 33 (.leaf (-22)) (.leaf (-21))) (.branch 54 (.leaf (-18)) (.leaf (-15)))) (.branch 57 (.branch 56 (.leaf (-12)) (.leaf (-9))) (.branch 58 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.leaf (-9)) (.branch 58 (.leaf (-6)) (.leaf (-3)))),
  (.branch 52 (.branch 48 (.branch 26 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 55 (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.leaf (-2))))))]
def witnessP9_301_5494 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (2)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (7)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (6))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (8)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (1))))))) (.branch 44 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (5)) (.leaf (0))))) (.branch 40 (.branch 38 (.leaf (2)) (.branch 39 (.leaf (1)) (.leaf (0)))) (.branch 42 (.branch 41 (.leaf (7)) (.leaf (0))) (.branch 43 (.leaf (1)) (.leaf (3)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (6))) (.branch 50 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.leaf (4)) (.branch 53 (.leaf (0)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (8)) (.leaf (0))) (.branch 57 (.leaf (2)) (.leaf (1))))))))
  code := certificateP9_5494
  counts := ![(.branch 27 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 13 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))) (.branch 42 (.branch 34 (.branch 30 (.leaf (11)) (.branch 31 (.leaf (12)) (.leaf (13)))) (.branch 37 (.leaf (14)) (.branch 40 (.leaf (15)) (.leaf (16))))) (.branch 51 (.branch 45 (.leaf (17)) (.branch 48 (.leaf (18)) (.leaf (19)))) (.branch 53 (.leaf (20)) (.branch 56 (.leaf (21)) (.leaf (22))))))),
  (.branch 29 (.branch 14 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 31 (.leaf (-24)) (.leaf (-30)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 35 (.leaf (-4)) (.leaf (-5)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-2)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (-16)) (.leaf (-17)))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (-5))) (.branch 52 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-22))),
  (.branch 20 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-17))),
  (.branch 26 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 43 (.branch 32 (.leaf (-30)) (.leaf (-29))) (.branch 54 (.leaf (-28)) (.branch 57 (.leaf (-26)) (.leaf (-19))))),
  (.branch 51 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.leaf (0)))),
  (.branch 48 (.leaf (-4)) (.leaf (-3))),
  (.branch 50 (.branch 46 (.branch 24 (.leaf (-17)) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.leaf (-11))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.leaf (-7)))) (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 55 (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3))))),
  (.branch 47 (.branch 41 (.branch 38 (.branch 37 (.leaf (-22)) (.leaf (-21))) (.branch 39 (.leaf (-20)) (.branch 40 (.leaf (-19)) (.leaf (-18))))) (.branch 44 (.branch 42 (.leaf (-17)) (.branch 43 (.leaf (-16)) (.leaf (-15)))) (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-13)) (.leaf (-12)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-10))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 53 (.branch 51 (.branch 50 (.leaf (-9)) (.leaf (-8))) (.branch 52 (.leaf (-7)) (.leaf (-6)))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 49 (.branch 45 (.branch 43 (.branch 42 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-15)) (.leaf (-14)))) (.branch 47 (.branch 46 (.leaf (-13)) (.leaf (-12))) (.branch 48 (.leaf (-11)) (.leaf (-10))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-9)) (.leaf (-8))) (.branch 52 (.leaf (-7)) (.leaf (-6)))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_301_5495 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (5)) (.leaf (7)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (6)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (5))))) (.branch 25 (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (8)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (4)) (.leaf (1))))))) (.branch 44 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (5)))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (0))) (.branch 36 (.leaf (1)) (.leaf (2))))) (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (7)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (3))) (.branch 43 (.leaf (0)) (.leaf (1)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (5)) (.branch 46 (.leaf (2)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (6)) (.leaf (0))) (.branch 50 (.leaf (1)) (.leaf (4))))) (.branch 54 (.branch 52 (.leaf (3)) (.branch 53 (.leaf (0)) (.leaf (8)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (2))) (.branch 57 (.leaf (5)) (.leaf (1))))))))
  code := certificateP9_5495
  counts := ![(.branch 26 (.branch 12 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 31 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 49 (.branch 43 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 55 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-4)) (.leaf (-5)))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 50 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-20))),
  (.branch 4 (.leaf (0)) (.leaf (-38))),
  (.branch 10 (.leaf (0)) (.branch 33 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-20)))),
  (.branch 11 (.leaf (0)) (.leaf (-18))),
  (.branch 25 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 51 (.leaf (-4)) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.branch 47 (.leaf (-7)) (.branch 57 (.leaf (-6)) (.leaf (-3)))),
  (.branch 54 (.branch 43 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3))))),
  (.branch 53 (.branch 40 (.branch 5 (.leaf (-38)) (.leaf (-37))) (.branch 52 (.leaf (-35)) (.leaf (-30)))) (.branch 55 (.branch 54 (.leaf (-25)) (.leaf (-20))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 34 (.leaf (-9)) (.branch 46 (.leaf (-7)) (.leaf (-5)))),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-18))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-14)) (.leaf (-12))))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 49 (.branch 44 (.branch 42 (.branch 41 (.leaf (-18)) (.leaf (-17))) (.branch 43 (.leaf (-16)) (.leaf (-15)))) (.branch 46 (.branch 45 (.leaf (-14)) (.leaf (-13))) (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-9)) (.leaf (-8))) (.branch 52 (.leaf (-7)) (.leaf (-6)))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_301_5496 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (7)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (4)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (8))) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (4))))) (.branch 25 (.branch 23 (.leaf (7)) (.branch 24 (.leaf (0)) (.leaf (6)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (3)) (.leaf (1))))))) (.branch 44 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (8)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (0))) (.branch 36 (.leaf (1)) (.leaf (2))))) (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (6)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (7))) (.branch 43 (.leaf (0)) (.leaf (1)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (4)) (.branch 46 (.leaf (2)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (5)) (.leaf (0))) (.branch 50 (.leaf (1)) (.leaf (3))))) (.branch 54 (.branch 52 (.leaf (8)) (.branch 53 (.leaf (0)) (.leaf (6)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (2))) (.branch 57 (.leaf (4)) (.leaf (1))))))))
  code := certificateP9_5496
  counts := ![(.branch 26 (.branch 12 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 31 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 49 (.branch 43 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 55 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-4)) (.leaf (-5)))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 50 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-5)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-38))),
  (.branch 10 (.leaf (0)) (.branch 33 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-20)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-49))),
  (.branch 13 (.leaf (0)) (.branch 32 (.leaf (-19)) (.leaf (-20))))]
  high := ![(.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 51 (.leaf (-4)) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.branch 47 (.leaf (-7)) (.branch 57 (.leaf (-6)) (.leaf (-3)))),
  (.branch 53 (.branch 40 (.branch 5 (.leaf (-38)) (.leaf (-37))) (.branch 52 (.leaf (-35)) (.leaf (-30)))) (.branch 55 (.branch 54 (.leaf (-25)) (.leaf (-20))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 34 (.leaf (-9)) (.branch 46 (.leaf (-7)) (.leaf (-5)))),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-18))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-14)) (.leaf (-12))))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2)))),
  (.branch 49 (.branch 45 (.branch 43 (.branch 4 (.leaf (-49)) (.leaf (-48))) (.branch 44 (.leaf (-45)) (.leaf (-42)))) (.branch 47 (.branch 46 (.leaf (-39)) (.leaf (-36))) (.branch 48 (.leaf (-33)) (.leaf (-30))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-27)) (.leaf (-24))) (.branch 52 (.leaf (-21)) (.leaf (-18)))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 54 (.branch 33 (.leaf (-20)) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_301_5497 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (7))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (5)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (1)) (.leaf (4))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (0))) (.branch 35 (.leaf (6)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 41 (.branch 40 (.leaf (5)) (.leaf (0))) (.branch 42 (.leaf (2)) (.leaf (4)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (0)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (3)) (.leaf (0))) (.branch 49 (.leaf (1)) (.leaf (8))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (2)) (.leaf (0))) (.branch 53 (.leaf (5)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (3))) (.branch 57 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_5497
  counts := ![(.branch 26 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.branch 38 (.leaf (12)) (.leaf (13))))) (.branch 48 (.branch 45 (.leaf (14)) (.leaf (15))) (.branch 52 (.leaf (16)) (.branch 55 (.leaf (17)) (.leaf (18))))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 49 (.leaf (9)) (.branch 54 (.leaf (10)) (.leaf (11)))))),
  (.branch 31 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 51 (.leaf (9)) (.branch 57 (.leaf (10)) (.leaf (11)))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-17)) (.leaf (-27)))) (.branch 32 (.leaf (-37)) (.branch 34 (.leaf (-40)) (.leaf (-50))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 17 (.leaf (-11)) (.branch 22 (.leaf (-13)) (.leaf (-14))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 46 (.leaf (-5)) (.branch 51 (.leaf (-6)) (.leaf (-7))))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-5)) (.leaf (-6)))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (-4))) (.branch 53 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-23))),
  (.branch 21 (.leaf (0)) (.leaf (-37))),
  (.branch 50 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 49 (.branch 35 (.leaf (-50)) (.branch 42 (.leaf (-49)) (.leaf (-48)))) (.branch 56 (.leaf (-47)) (.branch 57 (.leaf (-40)) (.leaf (-33))))),
  (.branch 56 (.branch 55 (.leaf (-14)) (.leaf (-11))) (.branch 57 (.leaf (-8)) (.leaf (-5)))),
  (.branch 52 (.leaf (-7)) (.leaf (-5))),
  (.branch 57 (.leaf (-6)) (.leaf (-3))),
  (.branch 44 (.leaf (-1)) (.leaf (0))),
  (.branch 55 (.branch 54 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3))))),
  (.branch 46 (.branch 40 (.branch 37 (.branch 36 (.leaf (-23)) (.leaf (-22))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-20)) (.leaf (-19))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))))) (.branch 52 (.branch 49 (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (-37)) (.leaf (-36))) (.branch 24 (.leaf (-35)) (.leaf (-34)))) (.branch 27 (.branch 26 (.leaf (-33)) (.leaf (-32))) (.branch 28 (.leaf (-31)) (.branch 29 (.leaf (-30)) (.leaf (-29)))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-28)) (.leaf (-27))) (.branch 33 (.leaf (-26)) (.leaf (-25)))) (.branch 36 (.branch 35 (.leaf (-24)) (.leaf (-23))) (.branch 37 (.leaf (-22)) (.branch 38 (.leaf (-21)) (.leaf (-20))))))) (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (-19)) (.leaf (-18))) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 45 (.branch 44 (.leaf (-15)) (.leaf (-14))) (.branch 46 (.leaf (-13)) (.branch 47 (.leaf (-12)) (.leaf (-11)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-8)) (.branch 52 (.leaf (-7)) (.leaf (-6))))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 54 (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_301_5498 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (7)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (8))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (5))) (.branch 28 (.leaf (1)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (0))) (.branch 35 (.leaf (7)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (6)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 41 (.branch 40 (.leaf (4)) (.leaf (0))) (.branch 42 (.leaf (2)) (.leaf (3)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (0)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (5)) (.leaf (0))) (.branch 49 (.leaf (1)) (.leaf (8))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (2)) (.leaf (0))) (.branch 53 (.leaf (4)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (6))) (.branch 57 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5498
  counts := ![(.branch 26 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.branch 38 (.leaf (12)) (.leaf (13))))) (.branch 48 (.branch 45 (.leaf (14)) (.leaf (15))) (.branch 52 (.leaf (16)) (.branch 55 (.leaf (17)) (.leaf (18))))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 49 (.leaf (9)) (.branch 54 (.leaf (10)) (.leaf (11)))))),
  (.branch 31 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 51 (.leaf (9)) (.branch 57 (.leaf (10)) (.leaf (11)))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-17)) (.leaf (-27)))) (.branch 32 (.leaf (-37)) (.branch 34 (.leaf (-40)) (.leaf (-50))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 17 (.leaf (-11)) (.branch 22 (.leaf (-13)) (.leaf (-14))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 46 (.leaf (-5)) (.branch 51 (.leaf (-6)) (.leaf (-7))))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (-4))) (.branch 53 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-34)) (.leaf (-35)))),
  (.branch 37 (.branch 18 (.leaf (0)) (.leaf (-4))) (.branch 56 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-23))),
  (.branch 21 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 49 (.branch 35 (.leaf (-50)) (.branch 42 (.leaf (-49)) (.leaf (-48)))) (.branch 56 (.leaf (-47)) (.branch 57 (.leaf (-40)) (.leaf (-33))))),
  (.branch 56 (.branch 55 (.leaf (-14)) (.leaf (-11))) (.branch 57 (.leaf (-8)) (.leaf (-5)))),
  (.branch 52 (.leaf (-7)) (.leaf (-5))),
  (.branch 44 (.leaf (-1)) (.leaf (0))),
  (.branch 55 (.branch 54 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3))))),
  (.branch 52 (.branch 49 (.branch 28 (.leaf (-35)) (.branch 48 (.leaf (-33)) (.leaf (-30)))) (.branch 50 (.leaf (-27)) (.branch 51 (.leaf (-24)) (.leaf (-21))))) (.branch 55 (.branch 53 (.leaf (-18)) (.branch 54 (.leaf (-15)) (.leaf (-12)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 57 (.leaf (-6)) (.leaf (-3))),
  (.branch 46 (.branch 40 (.branch 37 (.branch 36 (.leaf (-23)) (.leaf (-22))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-20)) (.leaf (-19))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))))) (.branch 52 (.branch 49 (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_301_5499 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (6)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (5))) (.branch 28 (.leaf (1)) (.leaf (4))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (7)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (1)) (.leaf (4)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (5)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (2))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (3)) (.leaf (0))) (.branch 53 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (8))) (.branch 57 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_5499
  counts := ![(.branch 26 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 52 (.leaf (18)) (.branch 55 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 34 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-3)) (.branch 52 (.leaf (-4)) (.leaf (-5))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 34 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 25 (.leaf (-11)) (.branch 54 (.leaf (-13)) (.leaf (-14))))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (-34))) (.branch 46 (.leaf (-35)) (.leaf (-36)))),
  (.branch 17 (.leaf (0)) (.leaf (-41))),
  (.branch 37 (.leaf (0)) (.leaf (-21))),
  (.branch 56 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 50 (.branch 46 (.leaf (-8)) (.leaf (-7))) (.branch 54 (.leaf (-6)) (.leaf (-5)))),
  (.branch 56 (.branch 55 (.leaf (-14)) (.leaf (-11))) (.branch 57 (.leaf (-8)) (.leaf (-5)))),
  (.branch 54 (.branch 52 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 53 (.leaf (-12)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.branch 44 (.leaf (-1)) (.leaf (0))),
  (.branch 52 (.branch 49 (.branch 47 (.leaf (-36)) (.branch 48 (.leaf (-33)) (.leaf (-30)))) (.branch 50 (.leaf (-27)) (.branch 51 (.leaf (-24)) (.leaf (-21))))) (.branch 55 (.branch 53 (.leaf (-18)) (.branch 54 (.leaf (-15)) (.leaf (-12)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 37 (.branch 27 (.branch 22 (.branch 19 (.branch 18 (.leaf (-41)) (.leaf (-40))) (.branch 20 (.leaf (-39)) (.branch 21 (.leaf (-38)) (.leaf (-37))))) (.branch 24 (.branch 23 (.leaf (-36)) (.leaf (-35))) (.branch 25 (.leaf (-34)) (.branch 26 (.leaf (-33)) (.leaf (-32)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (-31)) (.leaf (-30))) (.branch 30 (.leaf (-29)) (.branch 31 (.leaf (-28)) (.leaf (-27))))) (.branch 34 (.branch 33 (.leaf (-26)) (.leaf (-25))) (.branch 35 (.leaf (-24)) (.branch 36 (.leaf (-23)) (.leaf (-22))))))) (.branch 47 (.branch 42 (.branch 39 (.branch 38 (.leaf (-21)) (.leaf (-20))) (.branch 40 (.leaf (-19)) (.branch 41 (.leaf (-18)) (.leaf (-17))))) (.branch 44 (.branch 43 (.leaf (-16)) (.leaf (-15))) (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-13)) (.leaf (-12)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-10))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 42 (.branch 39 (.branch 38 (.leaf (-21)) (.leaf (-20))) (.branch 40 (.leaf (-19)) (.branch 41 (.leaf (-18)) (.leaf (-17))))) (.branch 44 (.branch 43 (.leaf (-16)) (.leaf (-15))) (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-13)) (.leaf (-12)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-10))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_301_5500 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (4)) (.leaf (0))) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (1)) (.leaf (6))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (1)) (.leaf (7)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (2))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (4)) (.leaf (0))) (.branch 53 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (3))) (.branch 57 (.leaf (1)) (.leaf (8))))))))
  code := certificateP9_5500
  counts := ![(.branch 26 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 52 (.leaf (18)) (.branch 55 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 34 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1))),
  (.branch 58 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-3)) (.branch 52 (.leaf (-4)) (.leaf (-5))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 34 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 25 (.leaf (-11)) (.branch 54 (.leaf (-13)) (.leaf (-14))))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 14 (.leaf (0)) (.leaf (-44))),
  (.branch 29 (.leaf (0)) (.leaf (-29))),
  (.branch 43 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 50 (.branch 46 (.leaf (-8)) (.leaf (-7))) (.branch 54 (.leaf (-6)) (.leaf (-5)))),
  (.branch 56 (.branch 55 (.leaf (-14)) (.leaf (-11))) (.branch 57 (.leaf (-8)) (.leaf (-5)))),
  (.branch 47 (.leaf (-7)) (.branch 57 (.leaf (-6)) (.leaf (-3)))),
  (.branch 54 (.branch 52 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 53 (.leaf (-12)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.branch 36 (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-44)) (.leaf (-43))) (.branch 17 (.leaf (-42)) (.branch 18 (.leaf (-41)) (.leaf (-40))))) (.branch 22 (.branch 20 (.leaf (-39)) (.branch 21 (.leaf (-38)) (.leaf (-37)))) (.branch 23 (.leaf (-36)) (.branch 24 (.leaf (-35)) (.leaf (-34)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-33)) (.leaf (-32))) (.branch 28 (.leaf (-31)) (.branch 29 (.leaf (-30)) (.leaf (-29))))) (.branch 33 (.branch 31 (.leaf (-28)) (.branch 32 (.leaf (-27)) (.leaf (-26)))) (.branch 34 (.leaf (-25)) (.branch 35 (.leaf (-24)) (.leaf (-23))))))) (.branch 47 (.branch 41 (.branch 38 (.branch 37 (.leaf (-22)) (.leaf (-21))) (.branch 39 (.leaf (-20)) (.branch 40 (.leaf (-19)) (.leaf (-18))))) (.branch 44 (.branch 42 (.leaf (-17)) (.branch 43 (.leaf (-16)) (.leaf (-15)))) (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-13)) (.leaf (-12)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-10))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (-29)) (.branch 31 (.leaf (-28)) (.leaf (-27)))) (.branch 34 (.branch 33 (.leaf (-26)) (.leaf (-25))) (.branch 35 (.leaf (-24)) (.leaf (-23))))) (.branch 39 (.branch 37 (.leaf (-22)) (.branch 38 (.leaf (-21)) (.leaf (-20)))) (.branch 41 (.branch 40 (.leaf (-19)) (.leaf (-18))) (.branch 42 (.leaf (-17)) (.leaf (-16)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-11))) (.branch 49 (.leaf (-10)) (.leaf (-9))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 46 (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-11))) (.branch 49 (.leaf (-10)) (.leaf (-9))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_301_5501 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (7)) (.leaf (0))) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (1)) (.leaf (6))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (1)) (.leaf (5)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (2))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (8)) (.leaf (0))) (.branch 53 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (3))) (.branch 57 (.leaf (1)) (.leaf (6))))))))
  code := certificateP9_5501
  counts := ![(.branch 26 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 52 (.leaf (18)) (.branch 55 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 34 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 29 (.leaf (0)) (.branch 58 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 51 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-3)) (.branch 52 (.leaf (-4)) (.leaf (-5))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 34 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 25 (.leaf (-11)) (.branch 54 (.leaf (-13)) (.leaf (-14))))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-22))),
  (.branch 14 (.leaf (0)) (.leaf (-15))),
  (.leaf (0)),
  (.branch 22 (.leaf (0)) (.leaf (-36))),
  (.branch 51 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 50 (.branch 46 (.leaf (-8)) (.leaf (-7))) (.branch 54 (.leaf (-6)) (.leaf (-5)))),
  (.branch 56 (.branch 55 (.leaf (-14)) (.leaf (-11))) (.branch 57 (.leaf (-8)) (.leaf (-5)))),
  (.branch 47 (.leaf (-7)) (.branch 57 (.leaf (-6)) (.leaf (-3)))),
  (.branch 47 (.branch 41 (.branch 38 (.branch 37 (.leaf (-22)) (.leaf (-21))) (.branch 39 (.leaf (-20)) (.branch 40 (.leaf (-19)) (.leaf (-18))))) (.branch 44 (.branch 42 (.leaf (-17)) (.branch 43 (.leaf (-16)) (.leaf (-15)))) (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-13)) (.leaf (-12)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-10))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 46 (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-11))) (.branch 49 (.leaf (-10)) (.leaf (-9))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 40 (.branch 31 (.branch 26 (.branch 24 (.branch 23 (.leaf (-36)) (.leaf (-35))) (.branch 25 (.leaf (-34)) (.leaf (-33)))) (.branch 28 (.branch 27 (.leaf (-32)) (.leaf (-31))) (.branch 29 (.leaf (-30)) (.branch 30 (.leaf (-29)) (.leaf (-28)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-27)) (.leaf (-26))) (.branch 34 (.leaf (-25)) (.leaf (-24)))) (.branch 37 (.branch 36 (.leaf (-23)) (.leaf (-22))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-20)) (.leaf (-19))))))) (.branch 49 (.branch 44 (.branch 42 (.branch 41 (.leaf (-18)) (.leaf (-17))) (.branch 43 (.leaf (-16)) (.leaf (-15)))) (.branch 46 (.branch 45 (.leaf (-14)) (.leaf (-13))) (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-9)) (.leaf (-8))) (.branch 52 (.leaf (-7)) (.leaf (-6)))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 54 (.branch 52 (.leaf (-7)) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_301_5502 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (7)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (6)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (8)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (5)) (.leaf (0))) (.branch 28 (.leaf (4)) (.leaf (2))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (3))) (.branch 35 (.leaf (0)) (.leaf (6))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (7)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (4)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (5)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (3)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (2)) (.leaf (0))) (.branch 53 (.leaf (8)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (6)) (.leaf (0))) (.branch 57 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_5502
  counts := ![(.branch 27 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 52 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 33 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 53 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-3)) (.branch 52 (.leaf (-4)) (.leaf (-5))))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.branch 33 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (-37))) (.branch 45 (.leaf (-38)) (.leaf (-39)))),
  (.branch 16 (.leaf (0)) (.leaf (-10))),
  (.branch 10 (.leaf (0)) (.leaf (-19))),
  (.branch 24 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 53 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 55 (.branch 49 (.leaf (-21)) (.leaf (-20))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 53 (.branch 52 (.leaf (-3)) (.leaf (-2))) (.branch 54 (.leaf (-1)) (.leaf (0)))),
  (.branch 53 (.branch 50 (.branch 35 (.leaf (-19)) (.leaf (-18))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-14)) (.leaf (-12))))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 43 (.leaf (-3)) (.leaf (-2))),
  (.branch 51 (.branch 48 (.branch 46 (.leaf (-39)) (.branch 47 (.leaf (-36)) (.leaf (-33)))) (.branch 49 (.leaf (-30)) (.branch 50 (.leaf (-27)) (.leaf (-24))))) (.branch 54 (.branch 52 (.leaf (-21)) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 56 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3)))),
  (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (-19)) (.leaf (-18))) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 45 (.branch 44 (.leaf (-15)) (.leaf (-14))) (.branch 46 (.leaf (-13)) (.branch 47 (.leaf (-12)) (.leaf (-11)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-8)) (.branch 52 (.leaf (-7)) (.leaf (-6))))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_301_5503 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (7))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (8)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (4)) (.leaf (5))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (3))) (.branch 35 (.leaf (0)) (.leaf (7))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (6)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (4)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (3)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (5))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (8)) (.leaf (3))) (.branch 53 (.leaf (0)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (4)) (.leaf (6))))))))
  code := certificateP9_5503
  counts := ![(.branch 27 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-19)) (.leaf (-28)))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-8)) (.branch 46 (.leaf (-11)) (.leaf (-13))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (-11))) (.branch 52 (.leaf (-17)) (.leaf (-22)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (-28))) (.branch 48 (.leaf (-29)) (.leaf (-30)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-22))),
  (.branch 22 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 45 (.branch 36 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.branch 42 (.leaf (-25)) (.leaf (-24))))) (.branch 51 (.branch 48 (.leaf (-23)) (.leaf (-22))) (.branch 54 (.leaf (-21)) (.branch 57 (.leaf (-20)) (.leaf (-10)))))),
  (.branch 44 (.branch 32 (.leaf (-19)) (.branch 38 (.leaf (-18)) (.leaf (-17)))) (.branch 56 (.branch 50 (.leaf (-16)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 55 (.branch 47 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-10)) (.branch 57 (.leaf (-8)) (.leaf (-6))))),
  (.branch 55 (.branch 53 (.leaf (-22)) (.branch 54 (.leaf (-20)) (.leaf (-18)))) (.branch 56 (.leaf (-16)) (.branch 57 (.leaf (-14)) (.leaf (-12))))),
  (.branch 43 (.leaf (-3)) (.leaf (-2))),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-30)) (.leaf (-27))) (.branch 51 (.leaf (-24)) (.branch 52 (.leaf (-21)) (.leaf (-18))))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 47 (.branch 41 (.branch 38 (.branch 37 (.leaf (-22)) (.leaf (-21))) (.branch 39 (.leaf (-20)) (.branch 40 (.leaf (-19)) (.leaf (-18))))) (.branch 44 (.branch 42 (.leaf (-17)) (.branch 43 (.leaf (-16)) (.leaf (-15)))) (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-13)) (.leaf (-12)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-10))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 52 (.leaf (-7)) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_301_5504 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (5))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (4))) (.branch 35 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (7)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (3)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (4)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (5))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (0)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (3)) (.leaf (8))))))))
  code := certificateP9_5504
  counts := ![(.branch 27 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 58 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-19)) (.leaf (-28)))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-8)) (.branch 46 (.leaf (-11)) (.leaf (-13))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-1)) (.leaf (-3)))) (.branch 42 (.leaf (-4)) (.branch 57 (.leaf (-6)) (.leaf (-7))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (-11))) (.branch 52 (.leaf (-17)) (.leaf (-22)))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (-28))) (.branch 48 (.leaf (-29)) (.leaf (-30)))),
  (.branch 19 (.leaf (0)) (.leaf (-39))),
  (.branch 39 (.leaf (0)) (.leaf (-19))),
  (.leaf (0))]
  high := ![(.branch 45 (.branch 36 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.branch 42 (.leaf (-25)) (.leaf (-24))))) (.branch 51 (.branch 48 (.leaf (-23)) (.leaf (-22))) (.branch 54 (.leaf (-21)) (.branch 57 (.leaf (-20)) (.leaf (-10)))))),
  (.branch 44 (.branch 32 (.leaf (-19)) (.branch 38 (.leaf (-18)) (.leaf (-17)))) (.branch 56 (.branch 50 (.leaf (-16)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 55 (.branch 47 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-10)) (.branch 57 (.leaf (-8)) (.leaf (-6))))),
  (.leaf (-7)),
  (.branch 55 (.branch 53 (.leaf (-22)) (.branch 54 (.leaf (-20)) (.leaf (-18)))) (.branch 56 (.leaf (-16)) (.branch 57 (.leaf (-14)) (.leaf (-12))))),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-30)) (.leaf (-27))) (.branch 51 (.leaf (-24)) (.branch 52 (.leaf (-21)) (.leaf (-18))))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 38 (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (-39)) (.leaf (-38))) (.branch 22 (.leaf (-37)) (.leaf (-36)))) (.branch 25 (.branch 24 (.leaf (-35)) (.leaf (-34))) (.branch 26 (.leaf (-33)) (.branch 27 (.leaf (-32)) (.leaf (-31)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-30)) (.leaf (-29))) (.branch 31 (.leaf (-28)) (.branch 32 (.leaf (-27)) (.leaf (-26))))) (.branch 35 (.branch 34 (.leaf (-25)) (.leaf (-24))) (.branch 36 (.leaf (-23)) (.branch 37 (.leaf (-22)) (.leaf (-21))))))) (.branch 48 (.branch 43 (.branch 40 (.branch 39 (.leaf (-20)) (.leaf (-19))) (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-17)) (.leaf (-16))))) (.branch 45 (.branch 44 (.leaf (-15)) (.leaf (-14))) (.branch 46 (.leaf (-13)) (.branch 47 (.leaf (-12)) (.leaf (-11)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-8)) (.branch 52 (.leaf (-7)) (.leaf (-6))))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (-19)) (.leaf (-18))) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 45 (.branch 44 (.leaf (-15)) (.leaf (-14))) (.branch 46 (.leaf (-13)) (.branch 47 (.leaf (-12)) (.leaf (-11)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-8)) (.branch 52 (.leaf (-7)) (.leaf (-6))))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_301_5505 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (4))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (8)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (2))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (5))) (.branch 28 (.leaf (1)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (4))) (.branch 35 (.leaf (3)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (6)) (.leaf (1)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (3))) (.branch 42 (.leaf (2)) (.leaf (0)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (5)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (4)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (0)) (.leaf (3))) (.branch 53 (.leaf (2)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (7))) (.branch 57 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5505
  counts := ![(.branch 26 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 32 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 55 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 50 (.leaf (9)) (.branch 54 (.leaf (10)) (.leaf (11)))))),
  (.branch 31 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 53 (.leaf (9)) (.branch 57 (.leaf (10)) (.leaf (11)))))),
  (.branch 29 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-5)))) (.branch 32 (.leaf (-6)) (.branch 43 (.leaf (-8)) (.leaf (-9))))),
  (.branch 28 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-17)) (.leaf (-19)))) (.branch 33 (.leaf (-22)) (.branch 54 (.leaf (-24)) (.leaf (-27))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 57 (.leaf (-10)) (.leaf (-12)))),
  (.branch 17 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (-12))) (.branch 45 (.leaf (-15)) (.leaf (-18)))),
  (.branch 38 (.leaf (0)) (.leaf (-20))),
  (.branch 56 (.leaf (0)) (.leaf (-2))),
  (.branch 16 (.leaf (0)) (.leaf (-42)))]
  high := ![(.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7)))),
  (.branch 56 (.branch 55 (.leaf (-27)) (.leaf (-22))) (.branch 57 (.leaf (-17)) (.leaf (-12)))),
  (.leaf (-12)),
  (.branch 47 (.leaf (-2)) (.branch 53 (.leaf (-1)) (.leaf (0)))),
  (.branch 53 (.branch 50 (.branch 35 (.leaf (-19)) (.leaf (-18))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-14)) (.leaf (-12))))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 51 (.branch 48 (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-17)) (.leaf (-16)))) (.branch 49 (.leaf (-15)) (.branch 50 (.leaf (-14)) (.leaf (-13))))) (.branch 54 (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 48 (.branch 43 (.branch 40 (.branch 39 (.leaf (-20)) (.leaf (-19))) (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-17)) (.leaf (-16))))) (.branch 45 (.branch 44 (.leaf (-15)) (.leaf (-14))) (.branch 46 (.leaf (-13)) (.branch 47 (.leaf (-12)) (.leaf (-11)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-8)) (.branch 52 (.leaf (-7)) (.leaf (-6))))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.leaf (-2)) (.leaf (-1))),
  (.branch 37 (.branch 26 (.branch 21 (.branch 18 (.branch 17 (.leaf (-42)) (.leaf (-41))) (.branch 19 (.leaf (-40)) (.branch 20 (.leaf (-39)) (.leaf (-38))))) (.branch 23 (.branch 22 (.leaf (-37)) (.leaf (-36))) (.branch 24 (.leaf (-35)) (.branch 25 (.leaf (-34)) (.leaf (-33)))))) (.branch 31 (.branch 28 (.branch 27 (.leaf (-32)) (.leaf (-31))) (.branch 29 (.leaf (-30)) (.branch 30 (.leaf (-29)) (.leaf (-28))))) (.branch 34 (.branch 32 (.leaf (-27)) (.branch 33 (.leaf (-26)) (.leaf (-25)))) (.branch 35 (.leaf (-24)) (.branch 36 (.leaf (-23)) (.leaf (-22))))))) (.branch 47 (.branch 42 (.branch 39 (.branch 38 (.leaf (-21)) (.leaf (-20))) (.branch 40 (.leaf (-19)) (.branch 41 (.leaf (-18)) (.leaf (-17))))) (.branch 44 (.branch 43 (.leaf (-16)) (.leaf (-15))) (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-13)) (.leaf (-12)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-10))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_301_5506 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (4))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (7)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (5)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (6)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (3)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (8)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (4)) (.branch 45 (.leaf (0)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (3))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (5)) (.leaf (0))) (.branch 53 (.leaf (4)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (6)) (.leaf (3))))))))
  code := certificateP9_5506
  counts := ![(.branch 27 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 36 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 45 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 52 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.leaf (0)) (.branch 57 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-3)) (.branch 52 (.leaf (-4)) (.leaf (-5))))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-8)) (.branch 46 (.leaf (-11)) (.leaf (-13))))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-14)) (.leaf (-15)))),
  (.branch 6 (.leaf (0)) (.branch 35 (.leaf (-9)) (.leaf (-10)))),
  (.branch 28 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-45))),
  (.branch 42 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 53 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 44 (.branch 32 (.leaf (-19)) (.branch 38 (.leaf (-18)) (.leaf (-17)))) (.branch 56 (.branch 50 (.leaf (-16)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 55 (.branch 47 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-10)) (.branch 57 (.leaf (-8)) (.leaf (-6))))),
  (.branch 49 (.leaf (-1)) (.leaf (0))),
  (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3))))),
  (.branch 54 (.branch 52 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.leaf (-7)))) (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-1)),
  (.branch 35 (.branch 24 (.branch 18 (.branch 15 (.branch 14 (.leaf (-45)) (.leaf (-44))) (.branch 16 (.leaf (-43)) (.branch 17 (.leaf (-42)) (.leaf (-41))))) (.branch 21 (.branch 19 (.leaf (-40)) (.branch 20 (.leaf (-39)) (.leaf (-38)))) (.branch 22 (.leaf (-37)) (.branch 23 (.leaf (-36)) (.leaf (-35)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-34)) (.leaf (-33))) (.branch 27 (.leaf (-32)) (.branch 28 (.leaf (-31)) (.leaf (-30))))) (.branch 32 (.branch 30 (.leaf (-29)) (.branch 31 (.leaf (-28)) (.leaf (-27)))) (.branch 33 (.leaf (-26)) (.branch 34 (.leaf (-25)) (.leaf (-24))))))) (.branch 46 (.branch 40 (.branch 37 (.branch 36 (.leaf (-23)) (.leaf (-22))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-20)) (.leaf (-19))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))))) (.branch 52 (.branch 49 (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 50 (.branch 46 (.branch 44 (.branch 43 (.leaf (-16)) (.leaf (-15))) (.branch 45 (.leaf (-14)) (.leaf (-13)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-11))) (.branch 49 (.leaf (-10)) (.leaf (-9))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_301_5507 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (4)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (6)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (4)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (7))) (.branch 35 (.leaf (0)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (4)) (.leaf (0)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (5)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (3))) (.branch 49 (.leaf (0)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (0)) (.leaf (8))) (.branch 53 (.leaf (0)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (4)) (.leaf (3))))))))
  code := certificateP9_5507
  counts := ![(.branch 27 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))) (.branch 43 (.branch 35 (.branch 30 (.leaf (11)) (.branch 32 (.leaf (12)) (.leaf (13)))) (.branch 37 (.leaf (14)) (.branch 40 (.leaf (15)) (.leaf (16))))) (.branch 51 (.branch 46 (.leaf (17)) (.branch 49 (.leaf (18)) (.leaf (19)))) (.branch 53 (.leaf (20)) (.branch 56 (.leaf (21)) (.leaf (22))))))),
  (.branch 26 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 24 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 8 (.leaf (-10)) (.leaf (-12)))) (.branch 37 (.branch 32 (.leaf (-14)) (.leaf (-15))) (.branch 53 (.leaf (-17)) (.leaf (-19))))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-20)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 39 (.leaf (-14)) (.leaf (-15)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (-15)) (.leaf (-17)))),
  (.branch 15 (.leaf (0)) (.leaf (-43))),
  (.branch 34 (.leaf (0)) (.leaf (-24))),
  (.branch 52 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 54 (.leaf (-19)) (.branch 57 (.leaf (-18)) (.leaf (-14)))),
  (.branch 51 (.branch 46 (.leaf (-20)) (.leaf (-19))) (.branch 56 (.leaf (-18)) (.branch 57 (.leaf (-12)) (.leaf (-6))))),
  (.branch 55 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-8)) (.leaf (-5))))),
  (.branch 39 (.leaf (-2)) (.branch 49 (.leaf (-1)) (.leaf (0)))),
  (.branch 43 (.leaf (-3)) (.leaf (-2))),
  (.branch 50 (.branch 46 (.branch 24 (.leaf (-17)) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.leaf (-11))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.leaf (-7)))) (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 36 (.branch 25 (.branch 20 (.branch 17 (.branch 16 (.leaf (-43)) (.leaf (-42))) (.branch 18 (.leaf (-41)) (.branch 19 (.leaf (-40)) (.leaf (-39))))) (.branch 22 (.branch 21 (.leaf (-38)) (.leaf (-37))) (.branch 23 (.leaf (-36)) (.branch 24 (.leaf (-35)) (.leaf (-34)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-33)) (.leaf (-32))) (.branch 28 (.leaf (-31)) (.branch 29 (.leaf (-30)) (.leaf (-29))))) (.branch 33 (.branch 31 (.leaf (-28)) (.branch 32 (.leaf (-27)) (.leaf (-26)))) (.branch 34 (.leaf (-25)) (.branch 35 (.leaf (-24)) (.leaf (-23))))))) (.branch 47 (.branch 41 (.branch 38 (.branch 37 (.leaf (-22)) (.leaf (-21))) (.branch 39 (.leaf (-20)) (.branch 40 (.leaf (-19)) (.leaf (-18))))) (.branch 44 (.branch 42 (.leaf (-17)) (.branch 43 (.leaf (-16)) (.leaf (-15)))) (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-13)) (.leaf (-12)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-10))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 46 (.branch 40 (.branch 37 (.branch 35 (.leaf (-24)) (.branch 36 (.leaf (-23)) (.leaf (-22)))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-20)) (.leaf (-19))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))))) (.branch 52 (.branch 49 (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_301_5508 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (7)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (6)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (8)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (6))) (.branch 35 (.leaf (0)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (0)) (.leaf (3)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (7)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (5)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (3))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (4)) (.leaf (6))) (.branch 53 (.leaf (0)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (8)) (.leaf (3))))))))
  code := certificateP9_5508
  counts := ![(.branch 27 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 57 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-19)) (.leaf (-28)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 36 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-8)) (.branch 46 (.leaf (-11)) (.leaf (-13))))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (-13)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (-16)) (.leaf (-19)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (-5))) (.branch 52 (.leaf (-8)) (.leaf (-11)))),
  (.branch 13 (.leaf (0)) (.leaf (-16))),
  (.branch 28 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 45 (.branch 36 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.branch 42 (.leaf (-25)) (.leaf (-24))))) (.branch 51 (.branch 48 (.leaf (-23)) (.leaf (-22))) (.branch 54 (.leaf (-21)) (.branch 57 (.leaf (-20)) (.leaf (-10)))))),
  (.branch 56 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 55 (.branch 47 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-10)) (.branch 57 (.leaf (-8)) (.leaf (-6))))),
  (.branch 49 (.leaf (-1)) (.leaf (0))),
  (.branch 54 (.branch 52 (.leaf (-14)) (.branch 53 (.leaf (-12)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.branch 51 (.branch 47 (.branch 24 (.leaf (-19)) (.branch 46 (.leaf (-18)) (.leaf (-17)))) (.branch 49 (.branch 48 (.leaf (-16)) (.leaf (-15))) (.branch 50 (.leaf (-14)) (.leaf (-13))))) (.branch 54 (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 55 (.branch 53 (.leaf (-11)) (.branch 54 (.leaf (-10)) (.leaf (-9)))) (.branch 56 (.leaf (-8)) (.branch 57 (.leaf (-7)) (.leaf (-6))))),
  (.branch 50 (.branch 46 (.branch 44 (.branch 43 (.leaf (-16)) (.leaf (-15))) (.branch 45 (.leaf (-14)) (.leaf (-13)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-11))) (.branch 49 (.leaf (-10)) (.leaf (-9))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_301_5509 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (5))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (7)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (4))) (.branch 13 (.leaf (2)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (6)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (5))) (.branch 20 (.leaf (8)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (4)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (7))) (.branch 28 (.leaf (6)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (5))) (.branch 35 (.leaf (4)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (8)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (1)) (.leaf (3))) (.branch 42 (.leaf (2)) (.leaf (0)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (6)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (7)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (3)) (.leaf (0)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (8))) (.branch 57 (.leaf (6)) (.leaf (4))))))))
  code := certificateP9_5509
  counts := ![(.branch 25 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 54 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 17 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 10 (.leaf (-5)) (.leaf (-6)))) (.branch 39 (.branch 32 (.leaf (-7)) (.leaf (-8))) (.branch 46 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-17)) (.leaf (-19)))),
  (.branch 6 (.leaf (0)) (.branch 29 (.leaf (-28)) (.leaf (-29)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-20)))),
  (.branch 28 (.leaf (0)) (.branch 57 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (-12)) (.leaf (-15)))),
  (.branch 38 (.branch 20 (.leaf (0)) (.leaf (-1))) (.branch 56 (.leaf (-4)) (.leaf (-7))))]
  high := ![(.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.leaf (-7)))),
  (.branch 51 (.branch 41 (.leaf (-21)) (.branch 46 (.leaf (-20)) (.leaf (-19)))) (.branch 56 (.leaf (-18)) (.branch 57 (.leaf (-12)) (.leaf (-6))))),
  (.branch 54 (.branch 43 (.leaf (-19)) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3))))),
  (.branch 54 (.branch 30 (.leaf (-29)) (.branch 42 (.leaf (-27)) (.leaf (-25)))) (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-18))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-14)) (.leaf (-12))))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (-3)),
  (.branch 53 (.branch 50 (.branch 28 (.leaf (-15)) (.leaf (-14))) (.branch 51 (.leaf (-13)) (.branch 52 (.leaf (-12)) (.leaf (-11))))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-9))) (.branch 56 (.leaf (-8)) (.branch 57 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 57 (.leaf (-7)) (.leaf (-6)))]
def witnessP9_301_5510 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (6))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (5)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (8)) (.leaf (2))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (1)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (6))) (.branch 35 (.leaf (3)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (1)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (3))) (.branch 42 (.leaf (2)) (.leaf (0)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (4)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (7)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (0)) (.leaf (3))) (.branch 53 (.leaf (2)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (5))) (.branch 57 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5510
  counts := ![(.branch 26 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 32 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 55 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 50 (.leaf (9)) (.branch 54 (.leaf (10)) (.leaf (11)))))),
  (.branch 31 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 53 (.leaf (9)) (.branch 57 (.leaf (10)) (.leaf (11)))))),
  (.branch 29 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 49 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-5)))) (.branch 32 (.leaf (-6)) (.branch 43 (.leaf (-8)) (.leaf (-9))))),
  (.branch 28 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-17)) (.leaf (-19)))) (.branch 33 (.leaf (-22)) (.branch 54 (.leaf (-24)) (.leaf (-27))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 57 (.leaf (-10)) (.leaf (-12)))),
  (.branch 17 (.leaf (0)) (.leaf (-2))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (-12))) (.branch 45 (.leaf (-15)) (.leaf (-18)))),
  (.branch 16 (.leaf (0)) (.branch 56 (.leaf (-5)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-24))),
  (.branch 49 (.leaf (0)) (.leaf (-9))),
  (.branch 20 (.leaf (0)) (.leaf (-38)))]
  high := ![(.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7)))),
  (.branch 56 (.branch 55 (.leaf (-27)) (.leaf (-22))) (.branch 57 (.leaf (-17)) (.leaf (-12)))),
  (.leaf (-12)),
  (.branch 47 (.leaf (-2)) (.branch 53 (.leaf (-1)) (.leaf (0)))),
  (.branch 51 (.branch 48 (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-17)) (.leaf (-16)))) (.branch 49 (.leaf (-15)) (.branch 50 (.leaf (-14)) (.leaf (-13))))) (.branch 54 (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 57 (.leaf (-7)) (.leaf (-6))),
  (.branch 46 (.branch 40 (.branch 37 (.branch 35 (.leaf (-24)) (.branch 36 (.leaf (-23)) (.leaf (-22)))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-20)) (.leaf (-19))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))))) (.branch 52 (.branch 49 (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 53 (.branch 51 (.branch 50 (.leaf (-9)) (.leaf (-8))) (.branch 52 (.leaf (-7)) (.leaf (-6)))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (-38)) (.leaf (-37))) (.branch 23 (.leaf (-36)) (.leaf (-35)))) (.branch 26 (.branch 25 (.leaf (-34)) (.leaf (-33))) (.branch 27 (.leaf (-32)) (.branch 28 (.leaf (-31)) (.leaf (-30)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-29)) (.leaf (-28))) (.branch 32 (.leaf (-27)) (.branch 33 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 35 (.leaf (-24)) (.leaf (-23))) (.branch 37 (.leaf (-22)) (.branch 38 (.leaf (-21)) (.leaf (-20))))))) (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (-19)) (.leaf (-18))) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 45 (.branch 44 (.leaf (-15)) (.leaf (-14))) (.branch 46 (.leaf (-13)) (.branch 47 (.leaf (-12)) (.leaf (-11)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-8)) (.branch 52 (.leaf (-7)) (.leaf (-6))))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_301_5511 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (7))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (8)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (4)) (.leaf (7))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (5))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (8))) (.branch 35 (.leaf (0)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (0)) (.leaf (6)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (3)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (7)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (5))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (4)) (.leaf (8))) (.branch 53 (.leaf (0)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (3)) (.leaf (6))))))))
  code := certificateP9_5511
  counts := ![(.branch 27 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-19)) (.leaf (-28)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 36 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-8)) (.branch 46 (.leaf (-11)) (.leaf (-13))))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (-13)) (.leaf (-14)))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (-28))) (.branch 48 (.leaf (-29)) (.leaf (-30)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (-16)) (.leaf (-19)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (-5))) (.branch 52 (.leaf (-8)) (.leaf (-11))))]
  high := ![(.branch 45 (.branch 36 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.branch 42 (.leaf (-25)) (.leaf (-24))))) (.branch 51 (.branch 48 (.leaf (-23)) (.leaf (-22))) (.branch 54 (.leaf (-21)) (.branch 57 (.leaf (-20)) (.leaf (-10)))))),
  (.branch 56 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 55 (.branch 47 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-10)) (.branch 57 (.leaf (-8)) (.leaf (-6))))),
  (.branch 43 (.leaf (-3)) (.leaf (-2))),
  (.branch 54 (.branch 52 (.leaf (-14)) (.branch 53 (.leaf (-12)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-30)) (.leaf (-27))) (.branch 51 (.leaf (-24)) (.branch 52 (.leaf (-21)) (.leaf (-18))))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 51 (.branch 47 (.branch 24 (.leaf (-19)) (.branch 46 (.leaf (-18)) (.leaf (-17)))) (.branch 49 (.branch 48 (.leaf (-16)) (.leaf (-15))) (.branch 50 (.leaf (-14)) (.leaf (-13))))) (.branch 54 (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 55 (.branch 53 (.leaf (-11)) (.branch 54 (.leaf (-10)) (.leaf (-9)))) (.branch 56 (.leaf (-8)) (.branch 57 (.leaf (-7)) (.leaf (-6)))))]
def witnessP9_301_5512 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (7))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (8)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (7)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (4))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (8))) (.branch 35 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (6)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (7)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (4)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (5))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (3)) (.leaf (0))) (.branch 53 (.leaf (8)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (6)) (.leaf (4))))))))
  code := certificateP9_5512
  counts := ![(.branch 27 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 52 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-3)) (.branch 52 (.leaf (-4)) (.leaf (-5))))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-8)) (.branch 46 (.leaf (-11)) (.leaf (-13))))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 29 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (-31)) (.leaf (-32)))),
  (.branch 38 (.branch 19 (.leaf (0)) (.leaf (-1))) (.branch 57 (.leaf (-2)) (.leaf (-3)))),
  (.branch 24 (.branch 5 (.leaf (0)) (.leaf (-15))) (.branch 42 (.leaf (-16)) (.leaf (-18)))),
  (.branch 13 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 53 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 44 (.branch 32 (.leaf (-19)) (.branch 38 (.leaf (-18)) (.leaf (-17)))) (.branch 56 (.branch 50 (.leaf (-16)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 55 (.branch 47 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-10)) (.branch 57 (.leaf (-8)) (.leaf (-6))))),
  (.branch 54 (.branch 52 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 53 (.leaf (-12)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 52 (.branch 49 (.branch 29 (.leaf (-32)) (.leaf (-30))) (.branch 50 (.leaf (-27)) (.branch 51 (.leaf (-24)) (.leaf (-21))))) (.branch 55 (.branch 53 (.leaf (-18)) (.branch 54 (.leaf (-15)) (.leaf (-12)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (-3)),
  (.branch 50 (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.leaf (-11))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.leaf (-7)))) (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 55 (.branch 54 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))))]
def witnessP9_301_5513 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (7))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (5))) (.branch 13 (.leaf (2)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (6)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (8))) (.branch 20 (.leaf (3)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (5)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (3))) (.branch 28 (.leaf (6)) (.leaf (4))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (7))) (.branch 35 (.leaf (5)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (1)) (.leaf (4))) (.branch 42 (.leaf (2)) (.leaf (0)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (6)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (5)) (.leaf (8))) (.branch 49 (.leaf (3)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (4)) (.leaf (0)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (3))) (.branch 57 (.leaf (6)) (.leaf (5))))))))
  code := certificateP9_5513
  counts := ![(.branch 25 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 54 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 17 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 10 (.leaf (-5)) (.leaf (-6)))) (.branch 39 (.branch 32 (.leaf (-7)) (.leaf (-8))) (.branch 46 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-17)) (.leaf (-19)))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (-3))) (.branch 56 (.leaf (-9)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.branch 29 (.leaf (-28)) (.leaf (-29)))),
  (.leaf (0)),
  (.branch 28 (.leaf (0)) (.branch 57 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-24))),
  (.branch 19 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.leaf (-7)))),
  (.branch 51 (.branch 41 (.leaf (-21)) (.branch 46 (.leaf (-20)) (.leaf (-19)))) (.branch 56 (.leaf (-18)) (.branch 57 (.leaf (-12)) (.leaf (-6))))),
  (.branch 54 (.branch 43 (.leaf (-19)) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.leaf (-14)) (.leaf (-12))),
  (.branch 54 (.branch 30 (.leaf (-29)) (.branch 42 (.leaf (-27)) (.leaf (-25)))) (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.leaf (-3)),
  (.branch 46 (.branch 40 (.branch 37 (.branch 35 (.leaf (-24)) (.branch 36 (.leaf (-23)) (.leaf (-22)))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-20)) (.leaf (-19))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))))) (.branch 52 (.branch 49 (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-8)) (.branch 52 (.leaf (-7)) (.leaf (-6))))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_301_5514 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (7)) (.branch 9 (.leaf (5)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (2)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (8))) (.branch 24 (.leaf (3)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (4)) (.leaf (5))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (3)) (.leaf (2))) (.branch 35 (.leaf (1)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (7)) (.branch 38 (.leaf (6)) (.leaf (4)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (5))) (.branch 49 (.leaf (2)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (0)) (.leaf (8))) (.branch 53 (.leaf (3)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (2))) (.branch 57 (.leaf (4)) (.leaf (6))))))))
  code := certificateP9_5514
  counts := ![(.branch 26 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 32 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 55 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 12 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 10 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 32 (.leaf (-31)) (.leaf (-36)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 25 (.leaf (-4)) (.branch 54 (.leaf (-5)) (.leaf (-6))))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (-1))) (.branch 46 (.leaf (-8)) (.leaf (-13)))),
  (.branch 9 (.leaf (0)) (.leaf (-31))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-21))),
  (.branch 23 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 52 (.branch 33 (.leaf (-36)) (.branch 48 (.leaf (-35)) (.leaf (-33)))) (.branch 56 (.leaf (-31)) (.branch 57 (.leaf (-24)) (.leaf (-17))))),
  (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 35 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-4)))),
  (.branch 54 (.branch 34 (.leaf (-17)) (.branch 44 (.leaf (-16)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3))))),
  (.branch 47 (.leaf (-13)) (.leaf (-12))),
  (.branch 52 (.branch 49 (.branch 10 (.leaf (-31)) (.leaf (-30))) (.branch 50 (.leaf (-27)) (.branch 51 (.leaf (-24)) (.leaf (-21))))) (.branch 55 (.branch 53 (.leaf (-18)) (.branch 54 (.leaf (-15)) (.leaf (-12)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 39 (.leaf (-2)) (.leaf (0))),
  (.branch 47 (.branch 42 (.branch 39 (.branch 38 (.leaf (-21)) (.leaf (-20))) (.branch 40 (.leaf (-19)) (.branch 41 (.leaf (-18)) (.leaf (-17))))) (.branch 44 (.branch 43 (.leaf (-16)) (.leaf (-15))) (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-13)) (.leaf (-12)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-10))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_301_5515 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (7)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (6)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (5)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (4)) (.leaf (0))) (.branch 24 (.leaf (8)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (6)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (0)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (7)))) (.branch 41 (.branch 40 (.leaf (3)) (.leaf (0))) (.branch 42 (.leaf (6)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (5)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (3)) (.leaf (0))) (.branch 53 (.leaf (8)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (2)) (.leaf (0))) (.branch 57 (.leaf (6)) (.leaf (4))))))))
  code := certificateP9_5515
  counts := ![(.branch 27 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 52 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 53 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-3)) (.branch 52 (.leaf (-4)) (.leaf (-5))))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-21)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-8)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 51 (.leaf (-8)) (.leaf (-9)))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (-1))) (.branch 33 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-19))),
  (.branch 24 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 53 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 55 (.branch 49 (.leaf (-21)) (.leaf (-20))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 56 (.branch 46 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3)))),
  (.branch 54 (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7)))) (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3))))),
  (.branch 47 (.branch 34 (.leaf (-3)) (.leaf (-2))) (.branch 48 (.leaf (-1)) (.leaf (0)))),
  (.branch 53 (.branch 50 (.branch 35 (.leaf (-19)) (.leaf (-18))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-14)) (.leaf (-12))))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 43 (.leaf (-3)) (.leaf (-2))),
  (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (-19)) (.leaf (-18))) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 45 (.branch 44 (.leaf (-15)) (.leaf (-14))) (.branch 46 (.leaf (-13)) (.branch 47 (.leaf (-12)) (.leaf (-11)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-8)) (.branch 52 (.leaf (-7)) (.leaf (-6))))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_301 : Fin 51 → CycleWitness 9 := ![witnessP9_301_5465, witnessP9_301_5466, witnessP9_301_5467, witnessP9_301_5468, witnessP9_301_5469, witnessP9_301_5470, witnessP9_301_5471, witnessP9_301_5472, witnessP9_301_5473, witnessP9_301_5474, witnessP9_301_5475, witnessP9_301_5476, witnessP9_301_5477, witnessP9_301_5478, witnessP9_301_5479, witnessP9_301_5480, witnessP9_301_5481, witnessP9_301_5482, witnessP9_301_5483, witnessP9_301_5484, witnessP9_301_5485, witnessP9_301_5486, witnessP9_301_5487, witnessP9_301_5488, witnessP9_301_5489, witnessP9_301_5490, witnessP9_301_5491, witnessP9_301_5492, witnessP9_301_5493, witnessP9_301_5494, witnessP9_301_5495, witnessP9_301_5496, witnessP9_301_5497, witnessP9_301_5498, witnessP9_301_5499, witnessP9_301_5500, witnessP9_301_5501, witnessP9_301_5502, witnessP9_301_5503, witnessP9_301_5504, witnessP9_301_5505, witnessP9_301_5506, witnessP9_301_5507, witnessP9_301_5508, witnessP9_301_5509, witnessP9_301_5510, witnessP9_301_5511, witnessP9_301_5512, witnessP9_301_5513, witnessP9_301_5514, witnessP9_301_5515]
end RealPinwheel.FiveSixths


