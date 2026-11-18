-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_029
-- name    : RealPinwheel_FiveSixths_WitnessD7_029
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:42:11.986802+00:00
-- url     : https://prove2.me/theorems/6a68eda9-8a4c-44b2-8d70-8853eb0e429c
-- title:
--   Exact witness block D7_029
-- statement:
--   These exact witnesses represent words 341 through 358 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 341–358; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_029_340 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (5)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (4))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (6)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (4)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (3)) (.leaf (0))) (.branch 41 (.leaf (1)) (.leaf (5)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (4)) (.leaf (2))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (6)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_340
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 54 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-18))) (.branch 18 (.leaf (-21)) (.leaf (-22)))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (-1))) (.branch 37 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-13)) (.leaf (-15)))),
  (.branch 14 (.leaf (0)) (.branch 51 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 51 (.leaf (-5)) (.branch 55 (.leaf (-4)) (.leaf (-2)))),
  (.branch 53 (.branch 47 (.leaf (-22)) (.leaf (-20))) (.branch 54 (.leaf (-15)) (.branch 55 (.leaf (-10)) (.leaf (-5))))),
  (.branch 33 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.branch 54 (.branch 46 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 49 (.branch 38 (.leaf (-3)) (.leaf (-2))) (.branch 50 (.leaf (-1)) (.leaf (0)))),
  (.branch 49 (.branch 45 (.branch 43 (.leaf (-15)) (.branch 44 (.leaf (-14)) (.leaf (-13)))) (.branch 47 (.branch 46 (.leaf (-12)) (.leaf (-11))) (.branch 48 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-7)) (.leaf (-6)))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 53 (.branch 52 (.leaf (-6)) (.leaf (-5))) (.branch 54 (.leaf (-4)) (.branch 55 (.leaf (-3)) (.leaf (-2)))))]
def witnessD7_029_341 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (6)) (.leaf (5))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (2)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (5)) (.leaf (0))) (.branch 34 (.leaf (6)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (3)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (5)) (.branch 44 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (6)) (.leaf (4))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (3)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (5))) (.branch 55 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_341
  counts := ![(.branch 25 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 44 (.branch 35 (.branch 30 (.leaf (7)) (.leaf (8))) (.branch 39 (.leaf (9)) (.leaf (10)))) (.branch 52 (.branch 47 (.leaf (11)) (.leaf (12))) (.branch 56 (.leaf (13)) (.leaf (14)))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 14 (.leaf (-14)) (.branch 42 (.leaf (-20)) (.leaf (-24))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 30 (.leaf (-8)) (.branch 47 (.leaf (-14)) (.leaf (-15))))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (-1))) (.branch 45 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 31 (.leaf (-13)) (.leaf (-14)))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-36))) (.branch 26 (.leaf (-37)) (.leaf (-38)))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (-6)) (.leaf (-7)))) (.branch 43 (.leaf (-8)) (.branch 54 (.leaf (-9)) (.leaf (-10))))),
  (.branch 6 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 54 (.branch 43 (.leaf (-24)) (.leaf (-23))) (.branch 55 (.leaf (-18)) (.leaf (-13)))),
  (.branch 53 (.branch 48 (.leaf (-15)) (.leaf (-13))) (.branch 54 (.leaf (-10)) (.branch 55 (.leaf (-7)) (.leaf (-4))))),
  (.branch 46 (.leaf (-5)) (.leaf (-4))),
  (.branch 52 (.branch 32 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 54 (.branch 53 (.leaf (-10)) (.leaf (-8))) (.branch 55 (.leaf (-6)) (.leaf (-4))))),
  (.branch 52 (.branch 50 (.branch 27 (.leaf (-38)) (.leaf (-35))) (.branch 51 (.leaf (-30)) (.leaf (-25)))) (.branch 54 (.branch 53 (.leaf (-20)) (.leaf (-15))) (.branch 55 (.leaf (-10)) (.leaf (-5))))),
  (.branch 55 (.leaf (-10)) (.leaf (-5))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_029_342 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (6)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (4)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (3))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (4)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (3)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (6)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (4)) (.leaf (3)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (5)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (2))) (.branch 48 (.leaf (3)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (4)) (.branch 51 (.leaf (1)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (0))) (.branch 55 (.leaf (6)) (.leaf (3))))))))
  code := certificateD7_342
  counts := ![(.branch 26 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 40 (.branch 32 (.branch 29 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 49 (.branch 43 (.leaf (15)) (.branch 46 (.leaf (16)) (.leaf (17)))) (.branch 52 (.leaf (18)) (.branch 54 (.leaf (19)) (.leaf (20))))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 8 (.leaf (0)) (.branch 45 (.leaf (-32)) (.leaf (-33)))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 55 (.leaf (-10)) (.leaf (-5))),
  (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 49 (.leaf (-1)) (.leaf (0))),
  (.branch 52 (.branch 32 (.leaf (-19)) (.branch 51 (.leaf (-18)) (.leaf (-15)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-9))) (.branch 55 (.leaf (-6)) (.leaf (-3))))),
  (.branch 50 (.branch 47 (.branch 46 (.leaf (-33)) (.leaf (-30))) (.branch 48 (.leaf (-27)) (.branch 49 (.leaf (-24)) (.leaf (-21))))) (.branch 53 (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-15)) (.leaf (-12)))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 18 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))]
def witnessD7_029_343 : CycleWitness 7 where
  length := 55
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (4)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (1))) (.branch 26 (.leaf (3)) (.leaf (0))))))) (.branch 41 (.branch 34 (.branch 30 (.branch 28 (.leaf (6)) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (3))) (.branch 33 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 35 (.leaf (0)) (.branch 36 (.leaf (2)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (0)) (.leaf (6)))))) (.branch 48 (.branch 44 (.branch 42 (.leaf (2)) (.branch 43 (.leaf (4)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (3))) (.branch 47 (.leaf (2)) (.leaf (5))))) (.branch 51 (.branch 49 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (4)))) (.branch 53 (.branch 52 (.leaf (0)) (.leaf (2))) (.branch 54 (.leaf (3)) (.leaf (6))))))))
  code := certificateD7_343
  counts := ![(.branch 27 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 35 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.leaf (15)))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))) (.branch 30 (.leaf (-5)) (.branch 40 (.leaf (-6)) (.leaf (-8))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 14 (.leaf (-14)) (.leaf (-15)))) (.branch 31 (.branch 25 (.leaf (-16)) (.leaf (-20))) (.branch 37 (.leaf (-21)) (.leaf (-22))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 47 (.leaf (-8)) (.branch 53 (.leaf (-10)) (.leaf (-11))))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-16)) (.leaf (-17)))) (.branch 33 (.leaf (-18)) (.branch 51 (.leaf (-19)) (.leaf (-21))))),
  (.branch 7 (.leaf (0)) (.branch 34 (.leaf (-27)) (.leaf (-29)))),
  (.branch 13 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))),
  (.branch 52 (.branch 38 (.leaf (-22)) (.branch 51 (.leaf (-21)) (.leaf (-18)))) (.branch 53 (.leaf (-15)) (.branch 54 (.leaf (-12)) (.leaf (-9))))),
  (.branch 54 (.leaf (-11)) (.leaf (-9))),
  (.branch 47 (.leaf (-3)) (.leaf (-2))),
  (.branch 53 (.branch 52 (.leaf (-21)) (.leaf (-16))) (.branch 54 (.leaf (-11)) (.leaf (-6)))),
  (.branch 51 (.branch 49 (.branch 35 (.leaf (-29)) (.leaf (-28))) (.branch 50 (.leaf (-24)) (.leaf (-20)))) (.branch 53 (.branch 52 (.leaf (-16)) (.leaf (-12))) (.branch 54 (.leaf (-8)) (.leaf (-4))))),
  (.branch 42 (.leaf (-1)) (.leaf (0)))]
def witnessD7_029_344 : CycleWitness 7 where
  length := 55
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (2)) (.leaf (5))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (0)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (3))))))) (.branch 41 (.branch 34 (.branch 30 (.branch 28 (.leaf (6)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (5))) (.branch 33 (.leaf (4)) (.leaf (3))))) (.branch 37 (.branch 35 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (3)) (.leaf (0))) (.branch 40 (.leaf (1)) (.leaf (4)))))) (.branch 48 (.branch 44 (.branch 42 (.leaf (2)) (.branch 43 (.leaf (0)) (.leaf (5)))) (.branch 46 (.branch 45 (.leaf (3)) (.leaf (1))) (.branch 47 (.leaf (6)) (.leaf (0))))) (.branch 51 (.branch 49 (.leaf (2)) (.branch 50 (.leaf (4)) (.leaf (3)))) (.branch 53 (.branch 52 (.leaf (1)) (.leaf (0))) (.branch 54 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_344
  counts := ![(.branch 26 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 39 (.branch 31 (.leaf (7)) (.branch 36 (.leaf (8)) (.leaf (9)))) (.branch 48 (.branch 43 (.leaf (10)) (.leaf (11))) (.branch 53 (.leaf (12)) (.leaf (13)))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 37 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 45 (.leaf (7)) (.branch 51 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 22 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 18 (.leaf (-8)) (.leaf (-9)))) (.branch 39 (.branch 26 (.leaf (-10)) (.leaf (-11))) (.branch 43 (.leaf (-12)) (.leaf (-13))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 12 (.leaf (-13)) (.branch 17 (.leaf (-15)) (.leaf (-17))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.branch 25 (.leaf (-1)) (.leaf (-2)))) (.branch 42 (.leaf (-5)) (.branch 54 (.leaf (-7)) (.leaf (-9))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-4)) (.leaf (-6)))) (.branch 38 (.branch 27 (.leaf (-7)) (.leaf (-8))) (.branch 51 (.leaf (-11)) (.leaf (-12))))),
  (.branch 41 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 50 (.leaf (-13)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (-15)) (.leaf (-18))))]
  high := ![(.branch 49 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 54 (.leaf (-11)) (.leaf (-9)))),
  (.branch 47 (.branch 18 (.leaf (-17)) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-11)) (.leaf (-8))))),
  (.leaf (-9)),
  (.branch 53 (.branch 52 (.leaf (-12)) (.leaf (-11))) (.branch 54 (.leaf (-10)) (.leaf (-9)))),
  (.branch 52 (.branch 51 (.leaf (-14)) (.leaf (-12))) (.branch 53 (.leaf (-10)) (.branch 54 (.leaf (-8)) (.leaf (-6))))),
  (.branch 33 (.branch 21 (.leaf (-6)) (.leaf (-5))) (.branch 45 (.leaf (-4)) (.branch 46 (.leaf (-2)) (.leaf (0))))),
  (.branch 50 (.branch 48 (.branch 29 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-15)) (.leaf (-13)))) (.branch 52 (.branch 51 (.leaf (-11)) (.leaf (-9))) (.branch 53 (.leaf (-7)) (.branch 54 (.leaf (-5)) (.leaf (-3))))))]
def witnessD7_029_345 : CycleWitness 7 where
  length := 54
  word := (.branch 27 (.branch 14 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.leaf (4)))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (0)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (5)) (.leaf (0))) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (6)) (.branch 26 (.leaf (0)) (.leaf (2))))))) (.branch 41 (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (0)) (.leaf (4)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (0)))))) (.branch 47 (.branch 44 (.branch 42 (.leaf (5)) (.leaf (0))) (.branch 45 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 48 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (6)) (.branch 53 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_345
  counts := ![(.branch 26 (.branch 13 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (9)) (.leaf (10))) (.branch 17 (.leaf (11)) (.leaf (12)))) (.branch 22 (.branch 20 (.leaf (13)) (.leaf (14))) (.branch 23 (.leaf (15)) (.branch 25 (.leaf (16)) (.leaf (17))))))) (.branch 40 (.branch 32 (.branch 29 (.branch 28 (.leaf (18)) (.leaf (19))) (.branch 31 (.leaf (20)) (.leaf (21)))) (.branch 35 (.branch 34 (.leaf (22)) (.leaf (23))) (.branch 37 (.leaf (24)) (.branch 38 (.leaf (25)) (.leaf (26)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (27)) (.leaf (28))) (.branch 44 (.leaf (29)) (.branch 46 (.leaf (30)) (.leaf (31))))) (.branch 50 (.branch 49 (.leaf (32)) (.leaf (33))) (.branch 52 (.leaf (34)) (.branch 53 (.leaf (35)) (.leaf (36)))))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-21))),
  (.branch 15 (.leaf (0)) (.leaf (-12))),
  (.branch 24 (.leaf (0)) (.leaf (-3)))]
  high := ![(.leaf (-2)),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 43 (.branch 38 (.branch 35 (.branch 34 (.leaf (-21)) (.leaf (-20))) (.branch 36 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17))))) (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_029_346 : CycleWitness 7 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 11 (.leaf (2)) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (0)) (.leaf (1))))))) (.branch 41 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (2)))))) (.branch 47 (.branch 44 (.branch 42 (.leaf (0)) (.branch 43 (.leaf (3)) (.leaf (0)))) (.branch 45 (.leaf (1)) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (6)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (3))) (.branch 53 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_346
  counts := ![(.branch 26 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 14 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))) (.branch 22 (.branch 20 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.leaf (13)))))) (.branch 40 (.branch 32 (.branch 28 (.leaf (14)) (.branch 30 (.leaf (15)) (.leaf (16)))) (.branch 37 (.branch 35 (.leaf (17)) (.leaf (18))) (.branch 38 (.leaf (19)) (.leaf (20))))) (.branch 46 (.branch 42 (.leaf (21)) (.branch 44 (.leaf (22)) (.leaf (23)))) (.branch 50 (.branch 48 (.leaf (24)) (.leaf (25))) (.branch 53 (.leaf (26)) (.leaf (27))))))),
  (.branch 27 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 45 (.leaf (7)) (.branch 51 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-41))),
  (.branch 31 (.leaf (0)) (.leaf (-23))),
  (.branch 49 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 48 (.leaf (-1)) (.leaf (0))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 33 (.branch 23 (.branch 18 (.branch 15 (.branch 14 (.leaf (-41)) (.leaf (-40))) (.branch 16 (.leaf (-39)) (.branch 17 (.leaf (-38)) (.leaf (-37))))) (.branch 20 (.branch 19 (.leaf (-36)) (.leaf (-35))) (.branch 21 (.leaf (-34)) (.branch 22 (.leaf (-33)) (.leaf (-32)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-31)) (.leaf (-30))) (.branch 26 (.leaf (-29)) (.branch 27 (.leaf (-28)) (.leaf (-27))))) (.branch 30 (.branch 29 (.leaf (-26)) (.leaf (-25))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22))))))) (.branch 43 (.branch 38 (.branch 35 (.branch 34 (.leaf (-21)) (.leaf (-20))) (.branch 36 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17))))) (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 36 (.branch 33 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_029_347 : CycleWitness 7 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (4)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (3)) (.leaf (0))))))) (.branch 41 (.branch 33 (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (5)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (2)))))) (.branch 47 (.branch 44 (.branch 42 (.leaf (1)) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 45 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (6)) (.branch 49 (.leaf (1)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (0))) (.branch 53 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_347
  counts := ![(.branch 25 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 20 (.leaf (9)) (.branch 22 (.leaf (10)) (.leaf (11)))))) (.branch 38 (.branch 32 (.branch 27 (.leaf (12)) (.branch 29 (.leaf (13)) (.leaf (14)))) (.branch 34 (.leaf (15)) (.branch 37 (.leaf (16)) (.leaf (17))))) (.branch 45 (.branch 40 (.leaf (18)) (.branch 43 (.leaf (19)) (.leaf (20)))) (.branch 50 (.branch 47 (.leaf (21)) (.leaf (22))) (.branch 52 (.leaf (23)) (.leaf (24))))))),
  (.branch 28 (.branch 13 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.leaf (15)))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 20 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 4 (.leaf (-8)) (.leaf (-9)))) (.branch 38 (.branch 22 (.leaf (-10)) (.leaf (-11))) (.branch 40 (.leaf (-12)) (.leaf (-13))))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 13 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-42))),
  (.branch 30 (.leaf (0)) (.leaf (-24))),
  (.branch 48 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 48 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-9)))),
  (.branch 50 (.leaf (-7)) (.leaf (-5))),
  (.branch 52 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 22 (.branch 17 (.branch 14 (.branch 13 (.leaf (-42)) (.leaf (-41))) (.branch 15 (.leaf (-40)) (.branch 16 (.leaf (-39)) (.leaf (-38))))) (.branch 19 (.branch 18 (.leaf (-37)) (.leaf (-36))) (.branch 20 (.leaf (-35)) (.branch 21 (.leaf (-34)) (.leaf (-33)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-32)) (.leaf (-31))) (.branch 25 (.leaf (-30)) (.branch 26 (.leaf (-29)) (.leaf (-28))))) (.branch 30 (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-26)) (.leaf (-25)))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22))))))) (.branch 43 (.branch 38 (.branch 35 (.branch 34 (.leaf (-21)) (.leaf (-20))) (.branch 36 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17))))) (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 36 (.branch 33 (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22)))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_029_348 : CycleWitness 7 where
  length := 54
  word := (.branch 27 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (3)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (0)))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (2))))))) (.branch 41 (.branch 34 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (0)) (.leaf (1))))) (.branch 38 (.branch 35 (.leaf (0)) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.leaf (1)) (.branch 40 (.leaf (0)) (.leaf (3)))))) (.branch 48 (.branch 44 (.branch 42 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (0)))) (.branch 45 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (1))))) (.branch 51 (.branch 49 (.leaf (0)) (.branch 50 (.leaf (6)) (.leaf (0)))) (.branch 52 (.leaf (1)) (.branch 53 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_348
  counts := ![(.branch 26 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 15 (.branch 13 (.leaf (7)) (.leaf (8))) (.branch 17 (.leaf (9)) (.leaf (10)))) (.branch 22 (.branch 20 (.leaf (11)) (.leaf (12))) (.branch 24 (.leaf (13)) (.leaf (14)))))) (.branch 40 (.branch 33 (.branch 29 (.branch 28 (.leaf (15)) (.leaf (16))) (.branch 31 (.leaf (17)) (.leaf (18)))) (.branch 37 (.branch 35 (.leaf (19)) (.leaf (20))) (.branch 38 (.leaf (21)) (.leaf (22))))) (.branch 47 (.branch 44 (.branch 42 (.leaf (23)) (.leaf (24))) (.branch 46 (.leaf (25)) (.leaf (26)))) (.branch 51 (.branch 49 (.leaf (27)) (.leaf (28))) (.branch 53 (.leaf (29)) (.leaf (30))))))),
  (.branch 25 (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-40))),
  (.branch 32 (.leaf (0)) (.leaf (-22))),
  (.branch 50 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 50 (.branch 48 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.leaf (-5)))),
  (.branch 53 (.leaf (-4)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 24 (.branch 19 (.branch 16 (.branch 15 (.leaf (-40)) (.leaf (-39))) (.branch 17 (.leaf (-38)) (.branch 18 (.leaf (-37)) (.leaf (-36))))) (.branch 21 (.branch 20 (.leaf (-35)) (.leaf (-34))) (.branch 22 (.leaf (-33)) (.branch 23 (.leaf (-32)) (.leaf (-31)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-30)) (.leaf (-29))) (.branch 27 (.leaf (-28)) (.branch 28 (.leaf (-27)) (.leaf (-26))))) (.branch 31 (.branch 30 (.leaf (-25)) (.leaf (-24))) (.branch 32 (.leaf (-23)) (.branch 33 (.leaf (-22)) (.leaf (-21))))))) (.branch 44 (.branch 39 (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16))))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 37 (.branch 34 (.branch 33 (.leaf (-22)) (.leaf (-21))) (.branch 35 (.leaf (-20)) (.branch 36 (.leaf (-19)) (.leaf (-18))))) (.branch 40 (.branch 38 (.leaf (-17)) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_029_349 : CycleWitness 7 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (1)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (3)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (5))))))) (.branch 41 (.branch 33 (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (3)) (.leaf (0)))))) (.branch 47 (.branch 44 (.branch 42 (.leaf (1)) (.branch 43 (.leaf (2)) (.leaf (0)))) (.branch 45 (.leaf (6)) (.branch 46 (.leaf (1)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (2)) (.branch 49 (.leaf (0)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (3)) (.leaf (0))) (.branch 53 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_349
  counts := ![(.branch 26 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 13 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 23 (.leaf (9)) (.leaf (10)))))) (.branch 38 (.branch 31 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.branch 37 (.leaf (14)) (.leaf (15))))) (.branch 47 (.branch 41 (.leaf (16)) (.branch 44 (.leaf (17)) (.leaf (18)))) (.branch 49 (.leaf (19)) (.branch 52 (.leaf (20)) (.leaf (21))))))),
  (.branch 28 (.branch 14 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.leaf (15)))))),
  (.branch 30 (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 20 (.leaf (-10)) (.branch 38 (.leaf (-12)) (.leaf (-14))))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (-6))) (.branch 40 (.leaf (-8)) (.leaf (-10)))),
  (.branch 9 (.leaf (0)) (.leaf (-45))),
  (.branch 27 (.leaf (0)) (.leaf (-27))),
  (.branch 45 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 50 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 53 (.leaf (-12)) (.leaf (-9)))),
  (.branch 43 (.leaf (-6)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 52 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.leaf (-7)))),
  (.branch 31 (.branch 20 (.branch 14 (.branch 11 (.branch 10 (.leaf (-45)) (.leaf (-44))) (.branch 12 (.leaf (-43)) (.branch 13 (.leaf (-42)) (.leaf (-41))))) (.branch 17 (.branch 15 (.leaf (-40)) (.branch 16 (.leaf (-39)) (.leaf (-38)))) (.branch 18 (.leaf (-37)) (.branch 19 (.leaf (-36)) (.leaf (-35)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-34)) (.leaf (-33))) (.branch 23 (.leaf (-32)) (.branch 24 (.leaf (-31)) (.leaf (-30))))) (.branch 28 (.branch 26 (.leaf (-29)) (.branch 27 (.leaf (-28)) (.leaf (-27)))) (.branch 29 (.leaf (-26)) (.branch 30 (.leaf (-25)) (.leaf (-24))))))) (.branch 42 (.branch 36 (.branch 33 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-26)) (.leaf (-25)))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22))))) (.branch 36 (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19)))) (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 39 (.leaf (-16)) (.leaf (-15)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_029_350 : CycleWitness 7 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (4)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (3)) (.leaf (0))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (2)) (.leaf (5)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (3)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (0)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (3)) (.leaf (0))) (.branch 46 (.leaf (1)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (6)) (.branch 49 (.leaf (0)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_350
  counts := ![(.branch 24 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 39 (.branch 31 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.branch 37 (.leaf (12)) (.leaf (13))))) (.branch 45 (.branch 42 (.leaf (14)) (.leaf (15))) (.branch 49 (.leaf (16)) (.branch 51 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 10 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))) (.branch 40 (.branch 32 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.branch 38 (.leaf (12)) (.leaf (13))))) (.branch 46 (.branch 43 (.leaf (14)) (.leaf (15))) (.branch 50 (.leaf (16)) (.branch 52 (.leaf (17)) (.leaf (18))))))),
  (.branch 29 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-42))),
  (.branch 30 (.leaf (0)) (.leaf (-24))),
  (.branch 48 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 48 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 33 (.branch 22 (.branch 17 (.branch 14 (.branch 13 (.leaf (-42)) (.leaf (-41))) (.branch 15 (.leaf (-40)) (.branch 16 (.leaf (-39)) (.leaf (-38))))) (.branch 19 (.branch 18 (.leaf (-37)) (.leaf (-36))) (.branch 20 (.leaf (-35)) (.branch 21 (.leaf (-34)) (.leaf (-33)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-32)) (.leaf (-31))) (.branch 25 (.leaf (-30)) (.branch 26 (.leaf (-29)) (.leaf (-28))))) (.branch 30 (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-26)) (.leaf (-25)))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22))))))) (.branch 43 (.branch 38 (.branch 35 (.branch 34 (.leaf (-21)) (.leaf (-20))) (.branch 36 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17))))) (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 36 (.branch 33 (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22)))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_029_351 : CycleWitness 7 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (5))) (.branch 26 (.leaf (1)) (.leaf (0))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (3)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (0)) (.leaf (6)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (0))) (.branch 46 (.leaf (1)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (3)) (.branch 49 (.leaf (1)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (0))) (.branch 53 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_351
  counts := ![(.branch 27 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))) (.branch 39 (.branch 32 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.branch 37 (.leaf (14)) (.leaf (15))))) (.branch 47 (.branch 42 (.leaf (16)) (.branch 45 (.leaf (17)) (.leaf (18)))) (.branch 50 (.leaf (19)) (.branch 52 (.leaf (20)) (.leaf (21))))))),
  (.branch 26 (.branch 10 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))) (.branch 40 (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.branch 38 (.leaf (12)) (.leaf (13))))) (.branch 46 (.branch 44 (.leaf (14)) (.leaf (15))) (.branch 49 (.leaf (16)) (.branch 53 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 12 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (-4)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-47))),
  (.branch 25 (.leaf (0)) (.leaf (-29))),
  (.branch 43 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 40 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-7)))),
  (.branch 50 (.leaf (-2)) (.leaf (-1))),
  (.branch 52 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 50 (.branch 37 (.leaf (-8)) (.branch 49 (.leaf (-7)) (.leaf (-6)))) (.branch 52 (.branch 51 (.leaf (-5)) (.leaf (-4))) (.branch 53 (.leaf (-3)) (.leaf (-2))))),
  (.branch 30 (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-47)) (.leaf (-46))) (.branch 10 (.leaf (-45)) (.branch 11 (.leaf (-44)) (.leaf (-43))))) (.branch 15 (.branch 13 (.leaf (-42)) (.branch 14 (.leaf (-41)) (.leaf (-40)))) (.branch 16 (.leaf (-39)) (.branch 17 (.leaf (-38)) (.leaf (-37)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-36)) (.branch 20 (.leaf (-35)) (.leaf (-34)))) (.branch 22 (.leaf (-33)) (.branch 23 (.leaf (-32)) (.leaf (-31))))) (.branch 27 (.branch 25 (.leaf (-30)) (.branch 26 (.leaf (-29)) (.leaf (-28)))) (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-26)) (.leaf (-25))))))) (.branch 42 (.branch 36 (.branch 33 (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22)))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 39 (.branch 32 (.branch 28 (.branch 26 (.leaf (-29)) (.branch 27 (.leaf (-28)) (.leaf (-27)))) (.branch 30 (.branch 29 (.leaf (-26)) (.leaf (-25))) (.branch 31 (.leaf (-24)) (.leaf (-23))))) (.branch 35 (.branch 33 (.leaf (-22)) (.branch 34 (.leaf (-21)) (.leaf (-20)))) (.branch 37 (.branch 36 (.leaf (-19)) (.leaf (-18))) (.branch 38 (.leaf (-17)) (.leaf (-16)))))) (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_029_352 : CycleWitness 7 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (6)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (5))) (.branch 26 (.leaf (0)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (6)) (.branch 35 (.leaf (0)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (4)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (5)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (3)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (6))) (.branch 53 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_352
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 14 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 23 (.leaf (10)) (.leaf (11)))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (12)) (.branch 30 (.leaf (13)) (.leaf (14)))) (.branch 35 (.leaf (15)) (.branch 37 (.leaf (16)) (.leaf (17))))) (.branch 46 (.branch 41 (.leaf (18)) (.branch 44 (.leaf (19)) (.leaf (20)))) (.branch 50 (.branch 48 (.leaf (21)) (.leaf (22))) (.branch 53 (.leaf (23)) (.leaf (24))))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (-9)) (.leaf (-10)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 51 (.leaf (-7)) (.leaf (-4))),
  (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 49 (.branch 46 (.branch 32 (.leaf (-19)) (.leaf (-18))) (.branch 47 (.leaf (-16)) (.branch 48 (.leaf (-14)) (.leaf (-12))))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 41 (.leaf (-1)) (.leaf (0))),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_029_353 : CycleWitness 7 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (6)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (5)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (3))) (.branch 26 (.leaf (0)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (4))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (6)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (3)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (5)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (4))) (.branch 53 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_353
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 14 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 23 (.leaf (10)) (.leaf (11)))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (12)) (.branch 30 (.leaf (13)) (.leaf (14)))) (.branch 35 (.leaf (15)) (.branch 37 (.leaf (16)) (.leaf (17))))) (.branch 46 (.branch 41 (.leaf (18)) (.branch 44 (.leaf (19)) (.leaf (20)))) (.branch 50 (.branch 48 (.leaf (21)) (.leaf (22))) (.branch 53 (.leaf (23)) (.leaf (24))))))),
  (.branch 24 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-17)) (.leaf (-19)))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-4)) (.branch 47 (.leaf (-5)) (.leaf (-7))))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-3))),
  (.branch 22 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-18)))]
  high := ![(.branch 51 (.leaf (-7)) (.leaf (-4))),
  (.branch 46 (.branch 35 (.leaf (-19)) (.leaf (-18))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-14)) (.leaf (-13))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_029_354 : CycleWitness 7 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (6)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (5))) (.branch 26 (.leaf (0)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (4)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (6)) (.branch 35 (.leaf (1)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (0))) (.branch 39 (.leaf (1)) (.leaf (2)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (4)) (.leaf (5)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (3)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (2)) (.branch 49 (.leaf (4)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (6))) (.branch 53 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_354
  counts := ![(.branch 26 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 38 (.branch 30 (.branch 28 (.leaf (10)) (.leaf (11))) (.branch 33 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14))))) (.branch 47 (.branch 41 (.leaf (15)) (.branch 44 (.leaf (16)) (.leaf (17)))) (.branch 50 (.leaf (18)) (.branch 53 (.leaf (19)) (.leaf (20))))))),
  (.branch 24 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))) (.branch 30 (.leaf (-15)) (.branch 38 (.leaf (-18)) (.leaf (-20))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 39 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (-9))) (.branch 49 (.leaf (-13)) (.leaf (-16)))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 45 (.branch 39 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 48 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-15))))),
  (.branch 46 (.branch 40 (.leaf (-10)) (.leaf (-9))) (.branch 52 (.leaf (-8)) (.branch 53 (.leaf (-6)) (.leaf (-4))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 51 (.branch 50 (.leaf (-16)) (.leaf (-14))) (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-10)) (.leaf (-8))))),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_029_355 : CycleWitness 7 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (3)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (5))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (3)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (6))) (.branch 46 (.leaf (1)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (2)) (.branch 49 (.leaf (0)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (3)) (.leaf (0))) (.branch 53 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_355
  counts := ![(.branch 26 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 13 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 23 (.leaf (9)) (.leaf (10)))))) (.branch 39 (.branch 31 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.branch 37 (.leaf (14)) (.leaf (15))))) (.branch 47 (.branch 41 (.leaf (16)) (.branch 44 (.leaf (17)) (.leaf (18)))) (.branch 49 (.leaf (19)) (.branch 52 (.leaf (20)) (.leaf (21))))))),
  (.branch 28 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.leaf (15)))))),
  (.branch 30 (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-8)) (.leaf (-11)))) (.branch 23 (.leaf (-14)) (.branch 41 (.leaf (-15)) (.leaf (-16))))),
  (.branch 20 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 38 (.leaf (-6)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (-6))) (.branch 40 (.leaf (-8)) (.leaf (-10)))),
  (.branch 9 (.leaf (0)) (.leaf (-45))),
  (.branch 27 (.leaf (0)) (.leaf (-27))),
  (.branch 45 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 50 (.branch 42 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-13)) (.leaf (-8)))),
  (.branch 39 (.leaf (-7)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 52 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.leaf (-7)))),
  (.branch 31 (.branch 20 (.branch 14 (.branch 11 (.branch 10 (.leaf (-45)) (.leaf (-44))) (.branch 12 (.leaf (-43)) (.branch 13 (.leaf (-42)) (.leaf (-41))))) (.branch 17 (.branch 15 (.leaf (-40)) (.branch 16 (.leaf (-39)) (.leaf (-38)))) (.branch 18 (.leaf (-37)) (.branch 19 (.leaf (-36)) (.leaf (-35)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-34)) (.leaf (-33))) (.branch 23 (.leaf (-32)) (.branch 24 (.leaf (-31)) (.leaf (-30))))) (.branch 28 (.branch 26 (.leaf (-29)) (.branch 27 (.leaf (-28)) (.leaf (-27)))) (.branch 29 (.leaf (-26)) (.branch 30 (.leaf (-25)) (.leaf (-24))))))) (.branch 42 (.branch 36 (.branch 33 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-26)) (.leaf (-25)))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22))))) (.branch 36 (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19)))) (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 39 (.leaf (-16)) (.leaf (-15)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_029_356 : CycleWitness 7 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (6))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (5))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (6)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (4))) (.branch 39 (.leaf (0)) (.leaf (2)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (3)) (.leaf (5))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (4)) (.leaf (0))) (.branch 53 (.leaf (2)) (.leaf (6))))))))
  code := certificateD7_356
  counts := ![(.branch 25 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 23 (.leaf (10)) (.leaf (11)))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (12)) (.branch 30 (.leaf (13)) (.leaf (14)))) (.branch 34 (.leaf (15)) (.branch 37 (.leaf (16)) (.leaf (17))))) (.branch 46 (.branch 41 (.leaf (18)) (.branch 43 (.leaf (19)) (.leaf (20)))) (.branch 50 (.branch 48 (.leaf (21)) (.leaf (22))) (.branch 52 (.leaf (23)) (.leaf (24))))))),
  (.branch 22 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.branch 7 (.leaf (-7)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-19)) (.leaf (-22)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-19)) (.leaf (-20)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 53 (.leaf (-8)) (.leaf (-4))),
  (.branch 50 (.branch 36 (.leaf (-22)) (.branch 43 (.leaf (-21)) (.leaf (-20)))) (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-12))) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-4)),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-18))) (.branch 47 (.leaf (-16)) (.branch 48 (.leaf (-14)) (.leaf (-12))))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_029_357 : CycleWitness 7 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (1)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (1)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (6)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (4))) (.branch 26 (.leaf (2)) (.leaf (5))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4))))) (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (6)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (3))) (.branch 39 (.leaf (0)) (.leaf (5)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (1)) (.leaf (4)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (3))) (.branch 46 (.leaf (1)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (6)) (.branch 49 (.leaf (2)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (4))) (.branch 53 (.leaf (3)) (.leaf (5))))))))
  code := certificateD7_357
  counts := ![(.branch 23 (.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 39 (.branch 31 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 50 (.leaf (13)) (.leaf (14)))))),
  (.branch 24 (.branch 10 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 29 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.leaf (7))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 23 (.leaf (-4)) (.branch 50 (.leaf (-5)) (.leaf (-6))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 32 (.leaf (-21)) (.leaf (-24)))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (-33))) (.branch 41 (.leaf (-36)) (.leaf (-37)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (-11)) (.leaf (-12))))]
  high := ![(.branch 52 (.branch 51 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 47 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 52 (.leaf (-21)) (.branch 53 (.leaf (-16)) (.leaf (-11))))),
  (.branch 51 (.branch 42 (.leaf (-37)) (.branch 50 (.leaf (-35)) (.leaf (-28)))) (.branch 52 (.leaf (-21)) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.branch 15 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-7)))),
  (.branch 34 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 41 (.leaf (-1)) (.leaf (0))),
  (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))]
def witnessD7_029 : Fin 18 → CycleWitness 7 := ![witnessD7_029_340, witnessD7_029_341, witnessD7_029_342, witnessD7_029_343, witnessD7_029_344, witnessD7_029_345, witnessD7_029_346, witnessD7_029_347, witnessD7_029_348, witnessD7_029_349, witnessD7_029_350, witnessD7_029_351, witnessD7_029_352, witnessD7_029_353, witnessD7_029_354, witnessD7_029_355, witnessD7_029_356, witnessD7_029_357]
end RealPinwheel.FiveSixths


