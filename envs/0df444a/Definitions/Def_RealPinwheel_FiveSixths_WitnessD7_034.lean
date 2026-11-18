-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_034
-- name    : RealPinwheel_FiveSixths_WitnessD7_034
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:44:17.797293+00:00
-- url     : https://prove2.me/theorems/a045c550-b7dc-4d57-8668-63c8e418750c
-- title:
--   Exact witness block D7_034
-- statement:
--   These exact witnesses represent words 434 through 453 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 434–453; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_034_433 : CycleWitness 7 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (3)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (6)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (5)) (.leaf (4))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (6)) (.branch 33 (.leaf (0)) (.leaf (2)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (3)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (4)) (.branch 39 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (5)) (.leaf (1))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (3)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (6)) (.leaf (4))))))))
  code := certificateD7_433
  counts := ![(.branch 22 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 22 (.leaf (-14)) (.branch 47 (.leaf (-16)) (.leaf (-17))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))) (.branch 14 (.leaf (-15)) (.branch 18 (.leaf (-16)) (.leaf (-17))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-14)) (.branch 21 (.leaf (-15)) (.leaf (-16))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-9))) (.branch 36 (.leaf (-12)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 32 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 44 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-12))) (.branch 49 (.leaf (-8)) (.leaf (-4)))),
  (.branch 47 (.branch 37 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 48 (.leaf (-8)) (.branch 49 (.leaf (-6)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 45 (.branch 43 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.leaf (-7)))) (.branch 47 (.branch 46 (.leaf (-6)) (.leaf (-5))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2)))))),
  (.leaf (-2))]
def witnessD7_034_434 : CycleWitness 7 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (1)) (.leaf (4))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (6)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (4)) (.leaf (2)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (3)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (5)) (.branch 39 (.leaf (0)) (.leaf (1)))) (.branch 41 (.leaf (2)) (.branch 42 (.leaf (4)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (3)) (.leaf (6)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (1)) (.leaf (4))))))))
  code := certificateD7_434
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 26 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.branch 27 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-13)) (.leaf (-14)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 20 (.leaf (-14)) (.leaf (-15)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (-35)) (.leaf (-37)))),
  (.branch 13 (.leaf (0)) (.branch 46 (.leaf (-11)) (.leaf (-12))))]
  high := ![(.branch 44 (.branch 27 (.leaf (-17)) (.leaf (-16))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 28 (.leaf (-12)) (.branch 45 (.leaf (-11)) (.leaf (-7)))),
  (.branch 48 (.branch 35 (.leaf (-14)) (.leaf (-12))) (.branch 49 (.leaf (-8)) (.leaf (-4)))),
  (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-12))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.leaf (-1)) (.leaf (0))),
  (.branch 43 (.branch 40 (.branch 22 (.leaf (-37)) (.branch 39 (.leaf (-36)) (.leaf (-33)))) (.branch 41 (.leaf (-30)) (.branch 42 (.leaf (-27)) (.leaf (-24))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-18)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3))))]
def witnessD7_034_435 : CycleWitness 7 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (5)) (.leaf (6)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (5)) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (2)) (.leaf (6))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (0)) (.leaf (2))))) (.branch 34 (.branch 32 (.leaf (4)) (.branch 33 (.leaf (1)) (.leaf (3)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (5)) (.leaf (6)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (2)) (.branch 39 (.leaf (0)) (.leaf (1)))) (.branch 41 (.leaf (4)) (.branch 42 (.leaf (3)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (5)) (.branch 45 (.leaf (2)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (4))) (.branch 49 (.leaf (3)) (.leaf (6))))))))
  code := certificateD7_435
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-19)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-17)) (.leaf (-18)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-25)) (.leaf (-32)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-7))) (.branch 20 (.leaf (-8)) (.branch 34 (.leaf (-9)) (.leaf (-11))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (-3))) (.branch 48 (.leaf (-5)) (.leaf (-6)))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-7)))) (.branch 36 (.leaf (-8)) (.branch 44 (.leaf (-9)) (.leaf (-10))))),
  (.branch 12 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 48 (.branch 31 (.leaf (-20)) (.leaf (-18))) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 47 (.branch 34 (.leaf (-18)) (.leaf (-16))) (.branch 48 (.leaf (-12)) (.branch 49 (.leaf (-8)) (.leaf (-4))))),
  (.branch 47 (.branch 10 (.leaf (-32)) (.branch 46 (.leaf (-31)) (.leaf (-25)))) (.branch 48 (.leaf (-19)) (.branch 49 (.leaf (-13)) (.leaf (-7))))),
  (.branch 35 (.leaf (-11)) (.leaf (-7))),
  (.branch 49 (.leaf (-6)) (.leaf (-4))),
  (.branch 47 (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8)))) (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5))))),
  (.branch 38 (.leaf (-1)) (.leaf (0)))]
def witnessD7_034_436 : CycleWitness 7 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (6)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (0))) (.branch 24 (.leaf (2)) (.leaf (1))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (6))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (4)) (.leaf (1)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (2)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (1)) (.branch 39 (.leaf (5)) (.leaf (0)))) (.branch 41 (.leaf (3)) (.branch 42 (.leaf (1)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (4)) (.branch 45 (.leaf (0)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (6)) (.leaf (0))) (.branch 49 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_436
  counts := ![(.branch 23 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))) (.branch 37 (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 43 (.branch 40 (.leaf (14)) (.leaf (15))) (.branch 45 (.leaf (16)) (.branch 48 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 46 (.branch 42 (.leaf (11)) (.leaf (12))) (.branch 50 (.leaf (13)) (.leaf (14)))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 20 (.leaf (-10)) (.branch 45 (.leaf (-12)) (.leaf (-13))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 27 (.leaf (-13)) (.branch 30 (.leaf (-17)) (.leaf (-21))))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (-5))) (.branch 44 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (-32)) (.leaf (-34)))),
  (.branch 14 (.leaf (0)) (.branch 47 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 46 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 43 (.branch 35 (.branch 31 (.leaf (-21)) (.leaf (-20))) (.branch 39 (.leaf (-19)) (.leaf (-18)))) (.branch 48 (.branch 47 (.leaf (-17)) (.leaf (-12))) (.branch 49 (.leaf (-7)) (.leaf (-2))))),
  (.branch 37 (.leaf (-3)) (.leaf (-2))),
  (.branch 45 (.branch 42 (.branch 29 (.leaf (-19)) (.leaf (-18))) (.branch 43 (.leaf (-16)) (.branch 44 (.leaf (-14)) (.leaf (-12))))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 47 (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.leaf (-5)) (.branch 49 (.leaf (-4)) (.leaf (-3))))),
  (.branch 44 (.branch 41 (.branch 23 (.leaf (-34)) (.branch 40 (.leaf (-33)) (.leaf (-30)))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-24)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))]
def witnessD7_034_437 : CycleWitness 7 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (3)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (2))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (4)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (5)) (.leaf (2))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (3)))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (0)) (.leaf (1)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (6)) (.branch 39 (.leaf (4)) (.leaf (0)))) (.branch 41 (.leaf (2)) (.branch 42 (.leaf (1)) (.leaf (3))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (5)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_437
  counts := ![(.branch 23 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 29 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 48 (.leaf (13)) (.leaf (14)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 42 (.leaf (8)) (.branch 47 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 10 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 31 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 43 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))) (.branch 29 (.leaf (-11)) (.branch 36 (.leaf (-12)) (.leaf (-13))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 13 (.leaf (0)) (.branch 46 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (-35)) (.leaf (-37))))]
  high := ![(.branch 41 (.branch 37 (.leaf (-13)) (.leaf (-12))) (.branch 45 (.leaf (-11)) (.branch 49 (.leaf (-10)) (.leaf (-7))))),
  (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3)))),
  (.branch 43 (.branch 40 (.branch 22 (.leaf (-37)) (.branch 39 (.leaf (-36)) (.leaf (-33)))) (.branch 41 (.leaf (-30)) (.branch 42 (.leaf (-27)) (.leaf (-24))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-18)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3))))))]
def witnessD7_034_438 : CycleWitness 7 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (1)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (6))) (.branch 24 (.leaf (2)) (.leaf (0))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (4)) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (2)) (.leaf (5))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (3)))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (0)) (.leaf (1)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (6)) (.branch 39 (.leaf (2)) (.leaf (3)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (4))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (5))) (.branch 49 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_438
  counts := ![(.branch 25 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 28 (.leaf (7)) (.branch 33 (.leaf (8)) (.leaf (9)))) (.branch 44 (.branch 41 (.leaf (10)) (.leaf (11))) (.branch 49 (.leaf (12)) (.leaf (13)))))),
  (.branch 22 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 42 (.leaf (9)) (.branch 47 (.leaf (10)) (.leaf (11)))))),
  (.branch 30 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 45 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-20)) (.leaf (-25)))) (.branch 19 (.leaf (-31)) (.branch 22 (.leaf (-37)) (.leaf (-50))))),
  (.branch 39 (.leaf (0)) (.leaf (-8))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-4)) (.leaf (-6)))) (.branch 40 (.branch 34 (.leaf (-7)) (.leaf (-8))) (.branch 46 (.leaf (-9)) (.leaf (-10))))),
  (.branch 10 (.leaf (0)) (.branch 26 (.leaf (-20)) (.leaf (-22)))),
  (.branch 14 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.branch 38 (.leaf (-14)) (.leaf (-16))))]
  high := ![(.branch 45 (.leaf (-4)) (.leaf (-3))),
  (.branch 38 (.branch 28 (.branch 23 (.leaf (-50)) (.leaf (-49))) (.branch 33 (.leaf (-48)) (.leaf (-47)))) (.branch 48 (.branch 43 (.leaf (-46)) (.leaf (-45))) (.branch 49 (.leaf (-38)) (.leaf (-31))))),
  (.branch 46 (.branch 40 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-2)) (.leaf (0)))),
  (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.leaf (-7)))),
  (.branch 46 (.branch 44 (.branch 27 (.leaf (-22)) (.leaf (-21))) (.branch 45 (.leaf (-18)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 32 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-3)))),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-16)) (.branch 40 (.leaf (-15)) (.leaf (-14)))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11))))) (.branch 47 (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8)))) (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5))))))]
def witnessD7_034_439 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 7 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 8 (.leaf (4)) (.branch 11 (.leaf (0)) (.leaf (2))))) (.branch 19 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (0)))) (.branch 20 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (5)))))) (.branch 36 (.branch 31 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (0)))) (.branch 32 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (1))))) (.branch 43 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (6)) (.leaf (0)))) (.branch 44 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_439
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (5))) (.branch 9 (.leaf (6)) (.branch 10 (.leaf (7)) (.leaf (8)))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (9)) (.leaf (10))) (.branch 15 (.leaf (11)) (.leaf (12)))) (.branch 19 (.branch 18 (.leaf (13)) (.leaf (14))) (.branch 21 (.leaf (15)) (.branch 22 (.leaf (16)) (.leaf (17))))))) (.branch 35 (.branch 29 (.branch 26 (.branch 25 (.leaf (18)) (.leaf (19))) (.branch 27 (.leaf (20)) (.leaf (21)))) (.branch 31 (.branch 30 (.leaf (22)) (.leaf (23))) (.branch 33 (.leaf (24)) (.branch 34 (.leaf (25)) (.leaf (26)))))) (.branch 42 (.branch 38 (.branch 37 (.leaf (27)) (.leaf (28))) (.branch 39 (.leaf (29)) (.branch 41 (.leaf (30)) (.leaf (31))))) (.branch 45 (.branch 43 (.leaf (32)) (.leaf (33))) (.branch 46 (.leaf (34)) (.branch 47 (.leaf (35)) (.leaf (36)))))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-1))) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-40))),
  (.branch 24 (.leaf (0)) (.leaf (-24))),
  (.branch 40 (.leaf (0)) (.leaf (-8)))]
  high := ![(.leaf (-3)),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 28 (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-40)) (.leaf (-39))) (.branch 11 (.leaf (-38)) (.branch 12 (.leaf (-37)) (.leaf (-36))))) (.branch 15 (.branch 14 (.leaf (-35)) (.leaf (-34))) (.branch 16 (.leaf (-33)) (.branch 17 (.leaf (-32)) (.leaf (-31)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-30)) (.leaf (-29))) (.branch 21 (.leaf (-28)) (.branch 22 (.leaf (-27)) (.leaf (-26))))) (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.branch 27 (.leaf (-22)) (.leaf (-21))))))) (.branch 38 (.branch 33 (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))) (.branch 33 (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_034_440 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.leaf (2)))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (4))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.leaf (5)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (3)))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (4))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (6)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_440
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.leaf (7))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (8)) (.leaf (9))) (.branch 16 (.leaf (10)) (.leaf (11)))) (.branch 20 (.branch 19 (.leaf (12)) (.leaf (13))) (.branch 22 (.leaf (14)) (.leaf (15)))))) (.branch 35 (.branch 29 (.branch 26 (.branch 25 (.leaf (16)) (.leaf (17))) (.branch 28 (.leaf (18)) (.leaf (19)))) (.branch 32 (.branch 31 (.leaf (20)) (.leaf (21))) (.branch 34 (.leaf (22)) (.leaf (23))))) (.branch 41 (.branch 38 (.branch 37 (.leaf (24)) (.leaf (25))) (.branch 40 (.leaf (26)) (.leaf (27)))) (.branch 44 (.branch 43 (.leaf (28)) (.leaf (29))) (.branch 46 (.leaf (30)) (.branch 47 (.leaf (31)) (.leaf (32)))))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-18))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-30))),
  (.branch 42 (.leaf (0)) (.leaf (-6)))]
  high := ![(.leaf (-2)),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 34 (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0)),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 25 (.branch 21 (.branch 19 (.leaf (-30)) (.branch 20 (.leaf (-29)) (.leaf (-28)))) (.branch 23 (.branch 22 (.leaf (-27)) (.leaf (-26))) (.branch 24 (.leaf (-25)) (.leaf (-24))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-23)) (.leaf (-22))) (.branch 28 (.leaf (-21)) (.leaf (-20)))) (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))))) (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_034_441 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 13 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.leaf (2)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (3))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (4)) (.leaf (0)))) (.branch 21 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (3))))))) (.branch 37 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (5))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (0)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 45 (.branch 43 (.leaf (1)) (.leaf (0))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_441
  counts := ![(.branch 23 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 17 (.branch 13 (.branch 12 (.leaf (7)) (.leaf (8))) (.branch 15 (.leaf (9)) (.leaf (10)))) (.branch 20 (.branch 18 (.leaf (11)) (.leaf (12))) (.branch 21 (.leaf (13)) (.leaf (14)))))) (.branch 36 (.branch 29 (.branch 26 (.branch 25 (.leaf (15)) (.leaf (16))) (.branch 28 (.leaf (17)) (.leaf (18)))) (.branch 33 (.branch 31 (.leaf (19)) (.leaf (20))) (.branch 34 (.leaf (21)) (.leaf (22))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (23)) (.leaf (24))) (.branch 41 (.leaf (25)) (.leaf (26)))) (.branch 45 (.branch 44 (.leaf (27)) (.leaf (28))) (.branch 47 (.leaf (29)) (.leaf (30))))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 16 (.leaf (0)) (.leaf (-32))),
  (.branch 32 (.leaf (0)) (.leaf (-16))),
  (.leaf (0))]
  high := ![(.branch 46 (.leaf (-7)) (.leaf (-5))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (-32)) (.leaf (-31))) (.branch 19 (.leaf (-30)) (.leaf (-29)))) (.branch 22 (.branch 21 (.leaf (-28)) (.leaf (-27))) (.branch 23 (.leaf (-26)) (.leaf (-25))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-24)) (.leaf (-23))) (.branch 27 (.leaf (-22)) (.leaf (-21)))) (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.leaf (-17)))))) (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_034_442 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (2))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.leaf (3)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (5))) (.branch 23 (.leaf (0)) (.leaf (2)))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 35 (.leaf (0)) (.leaf (2))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (6))) (.branch 47 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_442
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.leaf (7))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (8)) (.leaf (9))) (.branch 16 (.leaf (10)) (.leaf (11)))) (.branch 20 (.branch 19 (.leaf (12)) (.leaf (13))) (.branch 22 (.leaf (14)) (.leaf (15)))))) (.branch 35 (.branch 29 (.branch 26 (.branch 25 (.leaf (16)) (.leaf (17))) (.branch 28 (.leaf (18)) (.leaf (19)))) (.branch 32 (.branch 31 (.leaf (20)) (.leaf (21))) (.branch 34 (.leaf (22)) (.leaf (23))))) (.branch 41 (.branch 38 (.branch 37 (.leaf (24)) (.leaf (25))) (.branch 40 (.leaf (26)) (.leaf (27)))) (.branch 44 (.branch 43 (.leaf (28)) (.leaf (29))) (.branch 46 (.leaf (30)) (.branch 47 (.leaf (31)) (.leaf (32)))))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-27))),
  (.branch 45 (.leaf (0)) (.leaf (-3)))]
  high := ![(.leaf (-2)),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 27 (.branch 24 (.branch 22 (.leaf (-27)) (.branch 23 (.leaf (-26)) (.leaf (-25)))) (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22))))) (.branch 30 (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19)))) (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))))) (.branch 41 (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_034_443 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (6))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (4)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (1)) (.leaf (0))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (5))))))))
  code := certificateD7_443
  counts := ![(.branch 23 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 16 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))) (.branch 20 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 21 (.leaf (12)) (.leaf (13)))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (14)) (.branch 26 (.leaf (15)) (.leaf (16)))) (.branch 32 (.branch 30 (.leaf (17)) (.leaf (18))) (.branch 33 (.leaf (19)) (.leaf (20))))) (.branch 42 (.branch 38 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 40 (.leaf (23)) (.leaf (24)))) (.branch 45 (.branch 44 (.leaf (25)) (.leaf (26))) (.branch 47 (.leaf (27)) (.leaf (28))))))),
  (.branch 22 (.branch 10 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-36))),
  (.branch 36 (.leaf (0)) (.leaf (-12))),
  (.leaf (0)),
  (.branch 24 (.leaf (0)) (.leaf (-24)))]
  high := ![(.branch 39 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-7)))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 21 (.branch 16 (.branch 14 (.branch 13 (.leaf (-36)) (.leaf (-35))) (.branch 15 (.leaf (-34)) (.leaf (-33)))) (.branch 18 (.branch 17 (.leaf (-32)) (.leaf (-31))) (.branch 19 (.leaf (-30)) (.branch 20 (.leaf (-29)) (.leaf (-28)))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-27)) (.leaf (-26))) (.branch 24 (.leaf (-25)) (.leaf (-24)))) (.branch 27 (.branch 26 (.leaf (-23)) (.leaf (-22))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))))) (.branch 39 (.branch 34 (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))) (.branch 33 (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_034_444 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (3))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (4)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (6)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (1)) (.leaf (0))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_444
  counts := ![(.branch 23 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 16 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))) (.branch 20 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 21 (.leaf (12)) (.leaf (13)))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (14)) (.branch 26 (.leaf (15)) (.leaf (16)))) (.branch 32 (.branch 30 (.leaf (17)) (.leaf (18))) (.branch 33 (.leaf (19)) (.leaf (20))))) (.branch 42 (.branch 38 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 40 (.leaf (23)) (.leaf (24)))) (.branch 45 (.branch 44 (.leaf (25)) (.leaf (26))) (.branch 47 (.leaf (27)) (.leaf (28))))))),
  (.branch 22 (.branch 10 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 5 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.branch 17 (.leaf (0)) (.leaf (-31))),
  (.branch 41 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 39 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-7)))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 38 (.branch 33 (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0)),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 24 (.branch 20 (.branch 18 (.leaf (-31)) (.branch 19 (.leaf (-30)) (.leaf (-29)))) (.branch 22 (.branch 21 (.leaf (-28)) (.leaf (-27))) (.branch 23 (.leaf (-26)) (.leaf (-25))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-24)) (.leaf (-23))) (.branch 27 (.leaf (-22)) (.leaf (-21)))) (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.leaf (-17)))))) (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_034_445 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (6)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (4))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (5))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (4)) (.leaf (0))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (6)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (1)) (.leaf (0))) (.branch 46 (.leaf (4)) (.branch 47 (.leaf (0)) (.leaf (5))))))))
  code := certificateD7_445
  counts := ![(.branch 23 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 16 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))) (.branch 20 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 21 (.leaf (12)) (.leaf (13)))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (14)) (.branch 26 (.leaf (15)) (.leaf (16)))) (.branch 32 (.branch 30 (.leaf (17)) (.leaf (18))) (.branch 33 (.leaf (19)) (.leaf (20))))) (.branch 42 (.branch 38 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 40 (.leaf (23)) (.leaf (24)))) (.branch 45 (.branch 44 (.leaf (25)) (.leaf (26))) (.branch 47 (.leaf (27)) (.leaf (28))))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (-9)) (.leaf (-10)))),
  (.branch 15 (.leaf (0)) (.branch 46 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 39 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-7)))),
  (.branch 45 (.branch 35 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 40 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_034_446 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (0)))))) (.branch 18 (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (1))))))) (.branch 36 (.branch 29 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (3)) (.branch 28 (.leaf (0)) (.leaf (1))))) (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (5)) (.leaf (2)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (0)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_446
  counts := ![(.branch 23 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 12 (.leaf (5)) (.branch 14 (.leaf (6)) (.leaf (7)))) (.branch 18 (.leaf (8)) (.branch 21 (.leaf (9)) (.leaf (10)))))) (.branch 34 (.branch 28 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.branch 33 (.leaf (14)) (.leaf (15))))) (.branch 41 (.branch 37 (.leaf (16)) (.branch 39 (.leaf (17)) (.leaf (18)))) (.branch 44 (.leaf (19)) (.branch 46 (.leaf (20)) (.leaf (21))))))),
  (.branch 24 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 29 (.leaf (5)) (.leaf (6))) (.branch 40 (.leaf (7)) (.branch 45 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 10 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 48 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 18 (.leaf (-8)) (.branch 34 (.leaf (-9)) (.leaf (-10))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 13 (.leaf (-8)) (.leaf (-9)))),
  (.branch 26 (.branch 10 (.leaf (0)) (.leaf (-2))) (.branch 42 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 15 (.leaf (0)) (.leaf (-33))),
  (.branch 31 (.leaf (0)) (.leaf (-17))),
  (.branch 47 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 42 (.leaf (-10)) (.branch 47 (.leaf (-9)) (.leaf (-6)))),
  (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-6)) (.leaf (-3)))),
  (.branch 43 (.leaf (-4)) (.branch 44 (.leaf (-2)) (.leaf (0)))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (-33)) (.leaf (-32))) (.branch 18 (.leaf (-31)) (.leaf (-30)))) (.branch 21 (.branch 20 (.leaf (-29)) (.leaf (-28))) (.branch 22 (.leaf (-27)) (.leaf (-26))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 29 (.branch 28 (.leaf (-21)) (.leaf (-20))) (.branch 30 (.leaf (-19)) (.leaf (-18)))))) (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 37 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.leaf (-10))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 37 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.leaf (-10))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_034_447 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (4)) (.branch 29 (.leaf (0)) (.leaf (2))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (3)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (0)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (3)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_447
  counts := ![(.branch 22 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))) (.branch 34 (.branch 26 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 41 (.branch 37 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17)))) (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20))))))),
  (.branch 23 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 26 (.leaf (-7)) (.branch 38 (.leaf (-8)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-20))),
  (.branch 16 (.leaf (0)) (.leaf (-32))),
  (.branch 40 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 39 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-6)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 33 (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (-32)) (.leaf (-31))) (.branch 19 (.leaf (-30)) (.leaf (-29)))) (.branch 22 (.branch 21 (.leaf (-28)) (.leaf (-27))) (.branch 23 (.leaf (-26)) (.leaf (-25))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-24)) (.leaf (-23))) (.branch 27 (.leaf (-22)) (.leaf (-21)))) (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.leaf (-17)))))) (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_034_448 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 20 (.leaf (5)) (.leaf (0))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (1))))))) (.branch 36 (.branch 31 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0))))) (.branch 33 (.branch 32 (.leaf (4)) (.leaf (0))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (1)))))) (.branch 43 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (0))))) (.branch 45 (.branch 44 (.leaf (6)) (.leaf (0))) (.branch 46 (.leaf (3)) (.branch 47 (.leaf (0)) (.leaf (1))))))))
  code := certificateD7_448
  counts := ![(.branch 23 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 16 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))) (.branch 19 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 21 (.leaf (12)) (.leaf (13)))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (14)) (.branch 26 (.leaf (15)) (.leaf (16)))) (.branch 31 (.branch 30 (.leaf (17)) (.leaf (18))) (.branch 33 (.leaf (19)) (.leaf (20))))) (.branch 42 (.branch 38 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 40 (.leaf (23)) (.leaf (24)))) (.branch 45 (.branch 43 (.leaf (25)) (.leaf (26))) (.branch 47 (.leaf (27)) (.leaf (28))))))),
  (.branch 24 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 20 (.leaf (0)) (.leaf (-28))),
  (.branch 44 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 44 (.leaf (-11)) (.branch 46 (.leaf (-9)) (.leaf (-7)))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 27 (.branch 23 (.branch 21 (.leaf (-28)) (.branch 22 (.leaf (-27)) (.leaf (-26)))) (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.leaf (-22))))) (.branch 30 (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19)))) (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))))) (.branch 41 (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_034_449 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (4))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (6))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (5))))) (.branch 33 (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (1)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (6))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (1))))))))
  code := certificateD7_449
  counts := ![(.branch 22 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))) (.branch 34 (.branch 26 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 41 (.branch 37 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17)))) (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20))))))),
  (.branch 24 (.branch 12 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 26 (.leaf (-7)) (.branch 38 (.leaf (-8)) (.leaf (-9))))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-18))),
  (.branch 18 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 39 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 39 (.branch 34 (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_034_450 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (6)) (.leaf (0))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (4)))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (5))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 20 (.leaf (3)) (.leaf (0))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (6))))))) (.branch 36 (.branch 31 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0))))) (.branch 33 (.branch 32 (.leaf (5)) (.leaf (0))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (3)))))) (.branch 43 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (6))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (0))))) (.branch 45 (.branch 44 (.leaf (4)) (.leaf (0))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (5))))))))
  code := certificateD7_450
  counts := ![(.branch 23 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 16 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))) (.branch 19 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 21 (.leaf (12)) (.leaf (13)))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (14)) (.branch 26 (.leaf (15)) (.leaf (16)))) (.branch 31 (.branch 30 (.leaf (17)) (.leaf (18))) (.branch 33 (.leaf (19)) (.leaf (20))))) (.branch 42 (.branch 38 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 40 (.leaf (23)) (.leaf (24)))) (.branch 45 (.branch 43 (.leaf (25)) (.leaf (26))) (.branch 47 (.leaf (27)) (.leaf (28))))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.branch 27 (.leaf (-4)) (.leaf (-5)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 39 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 44 (.leaf (-11)) (.branch 46 (.leaf (-9)) (.leaf (-7)))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 41 (.branch 38 (.branch 4 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))) (.branch 39 (.leaf (-10)) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.leaf (-1)) (.leaf (0))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_034_451 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (5))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (5))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (4)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (1))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (6))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (4)))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (0)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (6))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (4)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_451
  counts := ![(.branch 22 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))) (.branch 35 (.branch 26 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 29 (.leaf (11)) (.branch 32 (.leaf (12)) (.leaf (13))))) (.branch 40 (.branch 38 (.leaf (14)) (.leaf (15))) (.branch 43 (.leaf (16)) (.branch 46 (.leaf (17)) (.leaf (18))))))),
  (.branch 24 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 26 (.leaf (-14)) (.leaf (-17)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-14)))),
  (.branch 10 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 41 (.branch 27 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-10))))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 41 (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_034_452 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (4))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (5)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_452
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 19 (.leaf (9)) (.branch 21 (.leaf (10)) (.leaf (11)))))) (.branch 35 (.branch 29 (.branch 25 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14)))) (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17))))) (.branch 41 (.branch 37 (.leaf (18)) (.branch 39 (.leaf (19)) (.leaf (20)))) (.branch 45 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 47 (.leaf (23)) (.leaf (24))))))),
  (.branch 22 (.branch 10 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 28 (.branch 26 (.leaf (8)) (.leaf (9))) (.branch 32 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 38 (.leaf (12)) (.leaf (13))) (.branch 44 (.leaf (14)) (.branch 46 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-36))),
  (.branch 24 (.leaf (0)) (.leaf (-24))),
  (.branch 36 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 21 (.branch 16 (.branch 14 (.branch 13 (.leaf (-36)) (.leaf (-35))) (.branch 15 (.leaf (-34)) (.leaf (-33)))) (.branch 18 (.branch 17 (.leaf (-32)) (.leaf (-31))) (.branch 19 (.leaf (-30)) (.branch 20 (.leaf (-29)) (.leaf (-28)))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-27)) (.leaf (-26))) (.branch 24 (.leaf (-25)) (.leaf (-24)))) (.branch 27 (.branch 26 (.leaf (-23)) (.leaf (-22))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))))) (.branch 39 (.branch 34 (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))) (.branch 33 (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_034 : Fin 20 → CycleWitness 7 := ![witnessD7_034_433, witnessD7_034_434, witnessD7_034_435, witnessD7_034_436, witnessD7_034_437, witnessD7_034_438, witnessD7_034_439, witnessD7_034_440, witnessD7_034_441, witnessD7_034_442, witnessD7_034_443, witnessD7_034_444, witnessD7_034_445, witnessD7_034_446, witnessD7_034_447, witnessD7_034_448, witnessD7_034_449, witnessD7_034_450, witnessD7_034_451, witnessD7_034_452]
end RealPinwheel.FiveSixths


