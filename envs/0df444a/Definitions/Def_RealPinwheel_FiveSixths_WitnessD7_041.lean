-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_041
-- name    : RealPinwheel_FiveSixths_WitnessD7_041
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:47:48.087216+00:00
-- url     : https://prove2.me/theorems/2b86624a-bc0e-49cf-acd7-5f0b91b40fb9
-- title:
--   Exact witness block D7_041
-- statement:
--   These exact witnesses represent words 581 through 603 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 581–603; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_041_580 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (6))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (5)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 20 (.leaf (4)) (.branch 21 (.leaf (1)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (3)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (2)) (.branch 29 (.leaf (6)) (.leaf (1)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (3)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (1)) (.leaf (2))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (5)) (.leaf (1))))) (.branch 41 (.branch 39 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 42 (.leaf (4)) (.branch 43 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_580
  counts := ![(.branch 19 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 25 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 38 (.leaf (8)) (.branch 43 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-17)) (.leaf (-19)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-9)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 39 (.leaf (-10)) (.leaf (-13)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 18 (.leaf (-11)) (.leaf (-12)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-13))) (.branch 24 (.leaf (-16)) (.leaf (-27)))),
  (.branch 13 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 37 (.branch 28 (.leaf (-19)) (.leaf (-18))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-10)) (.leaf (-5))))),
  (.branch 8 (.leaf (-9)) (.branch 39 (.leaf (-8)) (.leaf (-5)))),
  (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-11))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-7)) (.leaf (-5))))),
  (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 43 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.branch 38 (.branch 25 (.leaf (-27)) (.leaf (-26))) (.branch 39 (.leaf (-24)) (.leaf (-22)))) (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-18))) (.branch 43 (.leaf (-16)) (.leaf (-14))))),
  (.branch 14 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0))))]
def witnessD7_041_581 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (2)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (3)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (6)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (5)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (3))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (6))))) (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (3)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (4)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (5)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (2)) (.leaf (1))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (6)) (.leaf (2)))) (.branch 42 (.leaf (4)) (.branch 43 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_581
  counts := ![(.branch 21 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 25 (.leaf (5)) (.leaf (6))) (.branch 35 (.leaf (7)) (.branch 39 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 28 (.leaf (5)) (.leaf (6))) (.branch 38 (.leaf (7)) (.branch 43 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 10 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 29 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 41 (.leaf (-15)) (.leaf (-20)))),
  (.branch 10 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 22 (.leaf (-4)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-9)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-32))),
  (.branch 12 (.leaf (0)) (.branch 40 (.leaf (-3)) (.leaf (-5))))]
  high := ![(.branch 41 (.branch 40 (.leaf (-6)) (.leaf (-5))) (.branch 42 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2))))),
  (.branch 33 (.leaf (-3)) (.leaf (-2))),
  (.branch 42 (.leaf (-20)) (.branch 43 (.leaf (-16)) (.leaf (-12)))),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 41 (.branch 40 (.leaf (-3)) (.leaf (-2))) (.branch 42 (.leaf (-1)) (.leaf (0))))),
  (.branch 34 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-5)))),
  (.branch 38 (.branch 35 (.branch 5 (.leaf (-32)) (.branch 20 (.leaf (-31)) (.leaf (-30)))) (.branch 36 (.leaf (-27)) (.branch 37 (.leaf (-24)) (.leaf (-21))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-15)) (.leaf (-12)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.leaf (-2))))]
def witnessD7_041_582 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (4))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (5)) (.leaf (2)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (6))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (5)) (.leaf (1))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (1)) (.leaf (4))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (6)) (.leaf (2)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (3)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (1)) (.leaf (5))) (.branch 36 (.leaf (2)) (.branch 37 (.leaf (0)) (.leaf (4))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 42 (.leaf (2)) (.branch 43 (.leaf (6)) (.leaf (1))))))))
  code := certificateD7_582
  counts := ![(.branch 19 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 26 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 39 (.leaf (8)) (.branch 44 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 34 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 24 (.leaf (-11)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (-8))) (.branch 35 (.leaf (-9)) (.leaf (-10)))),
  (.branch 13 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 33 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-10)) (.leaf (-5))))),
  (.branch 40 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-1)) (.leaf (0)))),
  (.branch 31 (.branch 25 (.leaf (-13)) (.leaf (-12))) (.branch 37 (.leaf (-11)) (.branch 43 (.leaf (-10)) (.leaf (-7))))),
  (.branch 41 (.branch 26 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.leaf (-7)))) (.branch 41 (.branch 40 (.leaf (-6)) (.leaf (-5))) (.branch 42 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2)))))),
  (.leaf (-2))]
def witnessD7_041_583 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (4))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (5)) (.leaf (2)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (3)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (4)) (.leaf (2))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (6)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (4)) (.branch 21 (.leaf (0)) (.leaf (5))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (2))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (4))))) (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (5)) (.leaf (2)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (1)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (4)) (.leaf (2))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (6)) (.leaf (1))))) (.branch 41 (.branch 39 (.leaf (3)) (.branch 40 (.leaf (0)) (.leaf (2)))) (.branch 42 (.leaf (4)) (.branch 43 (.leaf (1)) (.leaf (5))))))))
  code := certificateD7_583
  counts := ![(.branch 21 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 26 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (7)) (.branch 40 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 28 (.leaf (5)) (.leaf (6))) (.branch 38 (.leaf (7)) (.branch 43 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 40 (.leaf (-35)) (.leaf (-36)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (-8)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 17 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 29 (.leaf (-7)) (.leaf (-13)))),
  (.branch 15 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 42 (.branch 41 (.leaf (-36)) (.leaf (-27))) (.branch 43 (.leaf (-18)) (.leaf (-9)))),
  (.branch 29 (.branch 19 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 34 (.leaf (-11)) (.branch 39 (.leaf (-10)) (.leaf (-9))))),
  (.branch 42 (.branch 36 (.leaf (-7)) (.leaf (-6))) (.branch 43 (.leaf (-4)) (.leaf (-2)))),
  (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 35 (.leaf (-8)) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 36 (.branch 32 (.branch 30 (.leaf (-13)) (.branch 31 (.leaf (-12)) (.leaf (-11)))) (.branch 34 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 41 (.branch 40 (.leaf (-3)) (.leaf (-2))) (.branch 42 (.leaf (-1)) (.leaf (0)))))),
  (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_041_584 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (1)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (5)) (.leaf (1)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (6)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (4)) (.leaf (3))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (5))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (3)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (4)) (.leaf (6))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (1)) (.leaf (3))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (4)) (.leaf (1)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (6)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (5)) (.leaf (3))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (4))))) (.branch 41 (.branch 39 (.leaf (2)) (.branch 40 (.leaf (0)) (.leaf (3)))) (.branch 42 (.leaf (1)) (.branch 43 (.leaf (5)) (.leaf (6))))))))
  code := certificateD7_584
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 43 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 40 (.leaf (-9)) (.leaf (-10)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 30 (.leaf (-10)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-16)) (.leaf (-17)))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 41 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-29)) (.leaf (-31)))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-8))) (.branch 43 (.leaf (-6)) (.leaf (-4)))),
  (.branch 37 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-7)))),
  (.branch 41 (.branch 32 (.leaf (-17)) (.branch 40 (.leaf (-15)) (.leaf (-12)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 42 (.leaf (-8)) (.branch 43 (.leaf (-6)) (.leaf (-4)))),
  (.branch 40 (.branch 30 (.leaf (-31)) (.branch 39 (.leaf (-30)) (.leaf (-25)))) (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-15))) (.branch 43 (.leaf (-10)) (.leaf (-5))))),
  (.branch 17 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5))))),
  (.leaf (0))]
def witnessD7_041_585 : CycleWitness 7 where
  length := 43
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (6)) (.leaf (1)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (3))))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (1))))) (.branch 29 (.branch 27 (.leaf (5)) (.branch 28 (.leaf (0)) (.leaf (3)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (1)) (.leaf (0)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (4)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (0)) (.leaf (3))))) (.branch 40 (.branch 38 (.leaf (1)) (.branch 39 (.leaf (6)) (.leaf (0)))) (.branch 41 (.leaf (2)) (.branch 42 (.leaf (1)) (.leaf (4))))))))
  code := certificateD7_585
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 36 (.leaf (9)) (.branch 40 (.leaf (10)) (.leaf (11)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 38 (.leaf (9)) (.branch 42 (.leaf (10)) (.leaf (11)))))),
  (.branch 19 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-32)) (.leaf (-39)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 35 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 37 (.leaf (-17)) (.leaf (-19)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 27 (.leaf (-31)) (.leaf (-32)))),
  (.branch 17 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 29 (.branch 21 (.branch 17 (.leaf (-39)) (.leaf (-38))) (.branch 25 (.leaf (-37)) (.leaf (-36)))) (.branch 37 (.branch 33 (.leaf (-35)) (.leaf (-34))) (.branch 41 (.leaf (-33)) (.branch 42 (.leaf (-22)) (.leaf (-11)))))),
  (.leaf (-2)),
  (.branch 36 (.leaf (-7)) (.branch 42 (.leaf (-6)) (.leaf (-4)))),
  (.branch 40 (.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-16)) (.leaf (-13)))) (.branch 41 (.leaf (-10)) (.branch 42 (.leaf (-7)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 35 (.branch 31 (.branch 29 (.branch 28 (.leaf (-32)) (.leaf (-30))) (.branch 30 (.leaf (-28)) (.leaf (-26)))) (.branch 33 (.branch 32 (.leaf (-24)) (.leaf (-22))) (.branch 34 (.leaf (-20)) (.leaf (-18))))) (.branch 39 (.branch 37 (.branch 36 (.leaf (-16)) (.leaf (-14))) (.branch 38 (.leaf (-12)) (.leaf (-10)))) (.branch 41 (.branch 40 (.leaf (-8)) (.leaf (-6))) (.branch 42 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 40 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 41 (.leaf (-6)) (.branch 42 (.leaf (-4)) (.leaf (-2)))))]
def witnessD7_041_586 : CycleWitness 7 where
  length := 43
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (4)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (6))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (4))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (6)) (.leaf (4))))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (1)) (.leaf (2))))) (.branch 29 (.branch 27 (.leaf (5)) (.branch 28 (.leaf (0)) (.leaf (4)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (3)) (.leaf (0)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (2)) (.leaf (1))) (.branch 35 (.leaf (6)) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 40 (.branch 38 (.leaf (4)) (.branch 39 (.leaf (3)) (.leaf (1)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (5)) (.leaf (2))))))))
  code := certificateD7_586
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 34 (.leaf (-7)) (.leaf (-9)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 26 (.leaf (-2)) (.branch 37 (.leaf (-4)) (.leaf (-5))))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-17)) (.leaf (-22)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-23))) (.branch 29 (.leaf (-26)) (.leaf (-27)))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (-15)) (.leaf (-18))))]
  high := ![(.branch 37 (.leaf (-9)) (.branch 42 (.leaf (-8)) (.leaf (-6)))),
  (.branch 41 (.branch 35 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-6)) (.leaf (-4)))),
  (.branch 40 (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3)))) (.branch 41 (.leaf (-2)) (.branch 42 (.leaf (-1)) (.leaf (0))))),
  (.branch 40 (.branch 10 (.leaf (-22)) (.branch 32 (.leaf (-21)) (.leaf (-18)))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-10)) (.leaf (-6))))),
  (.branch 40 (.branch 30 (.leaf (-27)) (.branch 39 (.leaf (-25)) (.leaf (-20)))) (.branch 41 (.leaf (-15)) (.branch 42 (.leaf (-10)) (.leaf (-5))))),
  (.branch 28 (.leaf (-5)) (.leaf (-3))),
  (.branch 38 (.branch 36 (.branch 21 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-15)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-11)) (.leaf (-9))) (.branch 41 (.leaf (-7)) (.branch 42 (.leaf (-5)) (.leaf (-3))))))]
def witnessD7_041_587 : CycleWitness 7 where
  length := 42
  word := (.branch 22 (.branch 10 (.branch 5 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 9 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 13 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (0)))))) (.branch 32 (.branch 25 (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (0)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_587
  counts := ![(.branch 21 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (5)) (.leaf (6))))) (.branch 15 (.branch 12 (.leaf (7)) (.branch 13 (.leaf (8)) (.leaf (9)))) (.branch 17 (.branch 16 (.leaf (10)) (.leaf (11))) (.branch 19 (.leaf (12)) (.leaf (13)))))) (.branch 31 (.branch 26 (.branch 22 (.leaf (14)) (.branch 24 (.leaf (15)) (.leaf (16)))) (.branch 29 (.branch 27 (.leaf (17)) (.leaf (18))) (.branch 30 (.leaf (19)) (.leaf (20))))) (.branch 36 (.branch 33 (.leaf (21)) (.branch 35 (.leaf (22)) (.leaf (23)))) (.branch 40 (.branch 38 (.leaf (24)) (.leaf (25))) (.branch 41 (.leaf (26)) (.leaf (27))))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 17 (.leaf (-9)) (.branch 31 (.leaf (-11)) (.leaf (-13))))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 14 (.leaf (0)) (.leaf (-28))),
  (.branch 28 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 32 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 21 (.branch 17 (.branch 15 (.leaf (-28)) (.branch 16 (.leaf (-27)) (.leaf (-26)))) (.branch 19 (.branch 18 (.leaf (-25)) (.leaf (-24))) (.branch 20 (.leaf (-23)) (.leaf (-22))))) (.branch 24 (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19)))) (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))))) (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_041_588 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 16 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (1))))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (2)) (.leaf (0))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (6))))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (0)) (.leaf (1))))))))
  code := certificateD7_588
  counts := ![(.branch 20 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 10 (.leaf (5)) (.branch 13 (.leaf (6)) (.leaf (7)))) (.branch 16 (.leaf (8)) (.branch 18 (.leaf (9)) (.leaf (10)))))) (.branch 30 (.branch 24 (.branch 22 (.leaf (11)) (.leaf (12))) (.branch 27 (.leaf (13)) (.branch 29 (.leaf (14)) (.leaf (15))))) (.branch 36 (.branch 32 (.leaf (16)) (.branch 34 (.leaf (17)) (.leaf (18)))) (.branch 38 (.leaf (19)) (.branch 41 (.leaf (20)) (.leaf (21))))))),
  (.branch 21 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 25 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-33))),
  (.branch 23 (.leaf (0)) (.leaf (-19))),
  (.branch 37 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-33)) (.leaf (-32))) (.branch 12 (.leaf (-31)) (.leaf (-30)))) (.branch 15 (.branch 14 (.leaf (-29)) (.leaf (-28))) (.branch 16 (.leaf (-27)) (.leaf (-26))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-25)) (.leaf (-24))) (.branch 20 (.leaf (-23)) (.leaf (-22)))) (.branch 23 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 24 (.leaf (-19)) (.leaf (-18)))))) (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 32 (.branch 27 (.branch 25 (.branch 24 (.leaf (-19)) (.leaf (-18))) (.branch 26 (.leaf (-17)) (.leaf (-16)))) (.branch 29 (.branch 28 (.leaf (-15)) (.leaf (-14))) (.branch 30 (.leaf (-13)) (.branch 31 (.leaf (-12)) (.leaf (-11)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6))))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_041_589 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 11 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (5)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (4)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (0))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (6))))))) (.branch 32 (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (5)) (.leaf (0)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (3)) (.leaf (0))) (.branch 35 (.leaf (1)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_589
  counts := ![(.branch 20 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 15 (.branch 11 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))) (.branch 16 (.leaf (9)) (.branch 18 (.leaf (10)) (.leaf (11)))))) (.branch 30 (.branch 25 (.branch 22 (.leaf (12)) (.branch 23 (.leaf (13)) (.leaf (14)))) (.branch 27 (.leaf (15)) (.branch 29 (.leaf (16)) (.leaf (17))))) (.branch 36 (.branch 32 (.leaf (18)) (.branch 34 (.leaf (19)) (.leaf (20)))) (.branch 39 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 41 (.leaf (23)) (.leaf (24))))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 38 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))),
  (.branch 38 (.branch 36 (.branch 25 (.leaf (-15)) (.leaf (-14))) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_041_590 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (4)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (1)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (1)) (.branch 30 (.leaf (3)) (.leaf (6)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_590
  counts := ![(.branch 18 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 23 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 34 (.branch 32 (.leaf (12)) (.leaf (13))) (.branch 38 (.leaf (14)) (.branch 39 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 24 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 18 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 7 (.leaf (-4)) (.leaf (-5)))) (.branch 28 (.branch 23 (.leaf (-6)) (.leaf (-7))) (.branch 39 (.leaf (-8)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 10 (.leaf (0)) (.leaf (-32))),
  (.branch 31 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7)))),
  (.branch 25 (.leaf (-6)) (.leaf (-5))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.branch 41 (.leaf (-4)) (.leaf (-2))),
  (.branch 38 (.branch 26 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 26 (.branch 18 (.branch 14 (.branch 12 (.branch 11 (.leaf (-32)) (.leaf (-31))) (.branch 13 (.leaf (-30)) (.leaf (-29)))) (.branch 16 (.branch 15 (.leaf (-28)) (.leaf (-27))) (.branch 17 (.leaf (-26)) (.leaf (-25))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-24)) (.leaf (-23))) (.branch 21 (.leaf (-22)) (.leaf (-21)))) (.branch 24 (.branch 23 (.leaf (-20)) (.leaf (-19))) (.branch 25 (.leaf (-18)) (.leaf (-17)))))) (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_041_591 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (5)))))) (.branch 16 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 17 (.leaf (6)) (.leaf (0))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (2))))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (5)) (.leaf (0)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (1)) (.leaf (0))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 38 (.leaf (6)) (.leaf (0))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_591
  counts := ![(.branch 20 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 11 (.leaf (5)) (.branch 13 (.leaf (6)) (.leaf (7)))) (.branch 16 (.leaf (8)) (.branch 18 (.leaf (9)) (.leaf (10)))))) (.branch 30 (.branch 25 (.branch 22 (.leaf (11)) (.leaf (12))) (.branch 27 (.leaf (13)) (.branch 29 (.leaf (14)) (.leaf (15))))) (.branch 36 (.branch 32 (.leaf (16)) (.branch 34 (.leaf (17)) (.leaf (18)))) (.branch 39 (.leaf (19)) (.branch 41 (.leaf (20)) (.leaf (21))))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-18))),
  (.branch 10 (.leaf (0)) (.leaf (-11))),
  (.branch 17 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 37 (.leaf (-2)) (.leaf (-1))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-14)) (.leaf (-13))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_041_592 : CycleWitness 7 where
  length := 42
  word := (.branch 22 (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (5))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (6))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (4)))))) (.branch 17 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (5))))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (0))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2))))))) (.branch 32 (.branch 27 (.branch 24 (.branch 23 (.leaf (6)) (.leaf (0))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (3))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (5)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (6)) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (4))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (0)) (.leaf (1))))))))
  code := certificateD7_592
  counts := ![(.branch 19 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 21 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (11)) (.branch 28 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 33 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 41 (.leaf (17)) (.leaf (18))))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 16 (.leaf (-14)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 37 (.leaf (-14)) (.leaf (-19)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-10)))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.branch 35 (.leaf (-13)) (.leaf (-17))))]
  high := ![(.branch 34 (.branch 29 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-11)))),
  (.branch 35 (.leaf (-1)) (.leaf (0))),
  (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-16))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-10)) (.leaf (-7))))),
  (.branch 30 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.leaf (-5)))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.branch 33 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 36 (.leaf (-17)) (.branch 37 (.leaf (-15)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-11)) (.leaf (-9))) (.branch 41 (.leaf (-7)) (.leaf (-5)))))]
def witnessD7_041_593 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (4))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (6)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (5)) (.leaf (4))))))))
  code := certificateD7_593
  counts := ![(.branch 19 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 33 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 40 (.leaf (17)) (.leaf (18))))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))) (.branch 35 (.branch 18 (.leaf (-10)) (.leaf (-11))) (.branch 39 (.leaf (-12)) (.leaf (-13))))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 34 (.leaf (-7)) (.leaf (-8)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 20 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 41 (.leaf (-6)) (.leaf (-3))),
  (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-10)) (.leaf (-7)))),
  (.branch 39 (.branch 26 (.leaf (-8)) (.branch 38 (.leaf (-7)) (.leaf (-6)))) (.branch 40 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-3))))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_041_594 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (5)) (.leaf (0))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (4))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (6)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (5)) (.leaf (4))))))))
  code := certificateD7_594
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 34 (.branch 32 (.leaf (12)) (.leaf (13))) (.branch 37 (.leaf (14)) (.branch 40 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 25 (.leaf (5)) (.leaf (6))) (.branch 35 (.leaf (7)) (.branch 39 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-12)) (.leaf (-17)))) (.branch 15 (.branch 10 (.leaf (-22)) (.leaf (-25))) (.branch 23 (.leaf (-28)) (.leaf (-29))))),
  (.branch 25 (.branch 2 (.leaf (0)) (.leaf (-14))) (.branch 39 (.leaf (-19)) (.leaf (-21)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 33 (.leaf (-8)) (.branch 38 (.leaf (-9)) (.leaf (-14))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (-11))) (.branch 24 (.leaf (-14)) (.leaf (-21)))),
  (.leaf (0)),
  (.branch 20 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 35 (.branch 24 (.leaf (-29)) (.leaf (-28))) (.branch 38 (.leaf (-26)) (.branch 41 (.leaf (-24)) (.leaf (-17))))),
  (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-16)) (.leaf (-11)))),
  (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-12))) (.branch 41 (.leaf (-10)) (.leaf (-8)))),
  (.branch 38 (.branch 25 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-18)))) (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-14))) (.branch 41 (.leaf (-12)) (.leaf (-10))))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 36 (.branch 33 (.branch 10 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_041_595 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (5)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (6)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_595
  counts := ![(.branch 20 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 34 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 41 (.leaf (17)) (.leaf (18))))))),
  (.branch 19 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-9))) (.branch 32 (.leaf (-15)) (.leaf (-20)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 18 (.leaf (0)) (.leaf (-24))),
  (.branch 39 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 39 (.leaf (-5)) (.leaf (-3))),
  (.branch 41 (.leaf (-4)) (.leaf (-2))),
  (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))),
  (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 30 (.branch 24 (.branch 21 (.branch 19 (.leaf (-24)) (.branch 20 (.leaf (-23)) (.leaf (-22)))) (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19))))) (.branch 27 (.branch 25 (.leaf (-18)) (.branch 26 (.leaf (-17)) (.leaf (-16)))) (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))))) (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_041_596 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (4)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (1))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (5))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (3))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (6))))))))
  code := certificateD7_596
  counts := ![(.branch 20 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 31 (.branch 26 (.branch 23 (.leaf (8)) (.leaf (9))) (.branch 29 (.leaf (10)) (.leaf (11)))) (.branch 37 (.branch 34 (.leaf (12)) (.leaf (13))) (.branch 40 (.leaf (14)) (.leaf (15)))))),
  (.branch 21 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 25 (.leaf (5)) (.leaf (6))) (.branch 35 (.leaf (7)) (.branch 39 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 27 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (7)) (.branch 41 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-2)) (.leaf (-4)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 24 (.leaf (-6)) (.branch 38 (.leaf (-8)) (.leaf (-10))))),
  (.branch 14 (.leaf (0)) (.leaf (-28))),
  (.branch 28 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 35 (.branch 32 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-6)) (.leaf (-3)))),
  (.branch 37 (.leaf (-4)) (.leaf (-3))),
  (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.leaf (-7)))),
  (.branch 28 (.branch 21 (.branch 17 (.branch 15 (.leaf (-28)) (.branch 16 (.leaf (-27)) (.leaf (-26)))) (.branch 19 (.branch 18 (.leaf (-25)) (.leaf (-24))) (.branch 20 (.leaf (-23)) (.leaf (-22))))) (.branch 24 (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19)))) (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))))) (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_041_597 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (5))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (6)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (1)) (.branch 30 (.leaf (0)) (.leaf (2)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (6)) (.leaf (5))))))))
  code := certificateD7_597
  counts := ![(.branch 19 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 30 (.branch 24 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 27 (.leaf (10)) (.leaf (11)))) (.branch 35 (.branch 32 (.leaf (12)) (.leaf (13))) (.branch 38 (.leaf (14)) (.branch 40 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-4)) (.leaf (-6)))) (.branch 31 (.leaf (-8)) (.branch 37 (.leaf (-9)) (.leaf (-11))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-8))) (.branch 33 (.leaf (-14)) (.leaf (-19)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 20 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 33 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-8)))),
  (.branch 40 (.branch 24 (.leaf (-13)) (.leaf (-12))) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))),
  (.branch 38 (.branch 22 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.leaf (-1))]
def witnessD7_041_598 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (1))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (1))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (3)) (.leaf (2)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (6)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (3)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (4))))))))
  code := certificateD7_598
  counts := ![(.branch 20 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 32 (.branch 26 (.branch 23 (.leaf (8)) (.leaf (9))) (.branch 29 (.leaf (10)) (.leaf (11)))) (.branch 37 (.branch 34 (.leaf (12)) (.leaf (13))) (.branch 40 (.leaf (14)) (.leaf (15)))))),
  (.branch 21 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 25 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 36 (.leaf (9)) (.branch 41 (.leaf (10)) (.leaf (11)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-19)) (.leaf (-23)))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 28 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 38 (.leaf (-14)) (.leaf (-16)))),
  (.branch 8 (.leaf (0)) (.branch 39 (.leaf (-8)) (.leaf (-11)))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-17)) (.leaf (-20)))),
  (.branch 16 (.leaf (0)) (.branch 35 (.leaf (-6)) (.leaf (-9))))]
  high := ![(.branch 35 (.branch 12 (.leaf (-23)) (.leaf (-22))) (.branch 38 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-13))))),
  (.branch 37 (.leaf (-4)) (.leaf (-3))),
  (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-13))) (.branch 41 (.leaf (-10)) (.leaf (-7)))),
  (.branch 40 (.leaf (-11)) (.branch 41 (.leaf (-8)) (.leaf (-5)))),
  (.branch 28 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 29 (.leaf (-2)) (.leaf (0)))),
  (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-20)) (.leaf (-19))) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 30 (.branch 29 (.leaf (-16)) (.leaf (-15))) (.branch 31 (.leaf (-14)) (.branch 32 (.leaf (-13)) (.leaf (-12)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.leaf (-8)))) (.branch 39 (.branch 38 (.leaf (-7)) (.leaf (-6))) (.branch 40 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-3))))))),
  (.branch 38 (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7)))) (.branch 40 (.branch 39 (.leaf (-6)) (.leaf (-5))) (.branch 41 (.leaf (-4)) (.leaf (-3)))))]
def witnessD7_041_599 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (4)))) (.branch 19 (.leaf (6)) (.branch 20 (.leaf (0)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (5))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (0)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (6))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (4)))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_599
  counts := ![(.branch 20 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 30 (.branch 24 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 27 (.leaf (10)) (.leaf (11)))) (.branch 35 (.branch 32 (.leaf (12)) (.leaf (13))) (.branch 38 (.leaf (14)) (.branch 41 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 24 (.leaf (-7)) (.leaf (-8)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 36 (.leaf (-15)) (.leaf (-18)))),
  (.branch 29 (.branch 4 (.leaf (0)) (.leaf (-9))) (.branch 37 (.leaf (-10)) (.leaf (-11)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 36 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))),
  (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-16)) (.leaf (-14)))) (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-10)) (.leaf (-8))))),
  (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-9))) (.branch 40 (.leaf (-7)) (.branch 41 (.leaf (-5)) (.leaf (-3))))),
  (.branch 17 (.leaf (-2)) (.branch 26 (.leaf (-1)) (.leaf (0)))),
  (.branch 40 (.branch 29 (.leaf (-7)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_041_600 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (3))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (6)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (0))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (5))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (6))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_600
  counts := ![(.branch 19 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 24 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 27 (.leaf (10)) (.leaf (11)))) (.branch 35 (.branch 32 (.leaf (12)) (.leaf (13))) (.branch 37 (.leaf (14)) (.branch 40 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 25 (.leaf (5)) (.leaf (6))) (.branch 34 (.leaf (7)) (.branch 39 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-23))) (.branch 5 (.leaf (-32)) (.leaf (-41)))),
  (.branch 25 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 34 (.leaf (-24)) (.leaf (-28)))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-22))))]
  high := ![(.branch 22 (.branch 6 (.leaf (-41)) (.branch 14 (.leaf (-40)) (.leaf (-39)))) (.branch 38 (.branch 30 (.leaf (-38)) (.leaf (-37))) (.branch 41 (.leaf (-32)) (.leaf (-18))))),
  (.branch 40 (.branch 35 (.leaf (-28)) (.leaf (-27))) (.branch 41 (.leaf (-21)) (.leaf (-15)))),
  (.branch 10 (.leaf (-3)) (.leaf (-2))),
  (.branch 38 (.branch 5 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 39 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 37 (.branch 34 (.branch 19 (.leaf (-22)) (.leaf (-21))) (.branch 35 (.leaf (-19)) (.branch 36 (.leaf (-17)) (.leaf (-15))))) (.branch 39 (.branch 38 (.leaf (-13)) (.leaf (-11))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-7)) (.leaf (-5))))))]
def witnessD7_041_601 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (5)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (4)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (6)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_601
  counts := ![(.branch 20 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 34 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 41 (.leaf (17)) (.leaf (18))))))),
  (.branch 19 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 11 (.leaf (0)) (.leaf (-10))),
  (.branch 18 (.leaf (0)) (.leaf (-24))),
  (.branch 39 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 39 (.leaf (-5)) (.leaf (-3))),
  (.branch 41 (.leaf (-4)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 34 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6))))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 30 (.branch 24 (.branch 21 (.branch 19 (.leaf (-24)) (.branch 20 (.leaf (-23)) (.leaf (-22)))) (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19))))) (.branch 27 (.branch 25 (.leaf (-18)) (.branch 26 (.leaf (-17)) (.leaf (-16)))) (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))))) (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_041_602 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (2)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (2))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (4)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (6)) (.leaf (2)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (4))))))))
  code := certificateD7_602
  counts := ![(.branch 19 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 24 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 27 (.leaf (10)) (.leaf (11)))) (.branch 34 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 37 (.leaf (14)) (.branch 40 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))) (.branch 29 (.branch 10 (.leaf (-12)) (.leaf (-15))) (.branch 31 (.leaf (-16)) (.leaf (-19))))),
  (.branch 2 (.leaf (0)) (.branch 23 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (-2)) (.leaf (-3)))),
  (.branch 17 (.leaf (0)) (.leaf (-25))),
  (.branch 38 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 35 (.branch 32 (.leaf (-19)) (.leaf (-18))) (.branch 38 (.leaf (-17)) (.branch 41 (.leaf (-16)) (.leaf (-12))))),
  (.branch 24 (.leaf (-10)) (.branch 37 (.leaf (-9)) (.leaf (-6)))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 36 (.leaf (-14)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 32 (.branch 31 (.leaf (-3)) (.leaf (-2))) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 29 (.branch 23 (.branch 20 (.branch 18 (.leaf (-25)) (.branch 19 (.leaf (-24)) (.leaf (-23)))) (.branch 21 (.leaf (-22)) (.branch 22 (.leaf (-21)) (.leaf (-20))))) (.branch 26 (.branch 24 (.leaf (-19)) (.branch 25 (.leaf (-18)) (.leaf (-17)))) (.branch 27 (.leaf (-16)) (.branch 28 (.leaf (-15)) (.leaf (-14)))))) (.branch 35 (.branch 32 (.branch 30 (.leaf (-13)) (.branch 31 (.leaf (-12)) (.leaf (-11)))) (.branch 33 (.leaf (-10)) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_041 : Fin 23 → CycleWitness 7 := ![witnessD7_041_580, witnessD7_041_581, witnessD7_041_582, witnessD7_041_583, witnessD7_041_584, witnessD7_041_585, witnessD7_041_586, witnessD7_041_587, witnessD7_041_588, witnessD7_041_589, witnessD7_041_590, witnessD7_041_591, witnessD7_041_592, witnessD7_041_593, witnessD7_041_594, witnessD7_041_595, witnessD7_041_596, witnessD7_041_597, witnessD7_041_598, witnessD7_041_599, witnessD7_041_600, witnessD7_041_601, witnessD7_041_602]
end RealPinwheel.FiveSixths


