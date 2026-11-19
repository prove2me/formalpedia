-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_312
-- name    : RealPinwheel_FiveSixths_WitnessP9_312
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:31:52.953521+00:00
-- url     : https://prove2.me/theorems/6ffd6816-6367-4a9b-9422-9df2994bf1b4
-- title:
--   Exact witness block P9_312
-- statement:
--   These exact witnesses represent words 6059 through 6116 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 6059–6116; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_312_6058 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (7)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (5)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (4)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (6)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (8)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (4)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (5)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (7)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (2)) (.branch 34 (.leaf (6)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (4)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (5)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (8)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (4)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (6)) (.leaf (2))))))))
  code := certificateP9_6058
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-10))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (-28))) (.branch 42 (.leaf (-29)) (.leaf (-30)))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 50 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 44 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.branch 30 (.leaf (-17)) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-30)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 17 (.leaf (-4)) (.leaf (-3))),
  (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_312_6059 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (8)))) (.branch 17 (.leaf (6)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (7))) (.branch 25 (.leaf (5)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 30 (.leaf (6)) (.branch 31 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (8)) (.branch 34 (.leaf (1)) (.leaf (3)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (7)))) (.branch 43 (.leaf (6)) (.branch 44 (.leaf (3)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (8))) (.branch 51 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_6059
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-10))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-19)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-31)) (.leaf (-32)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (-4))) (.branch 50 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 50 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 48 (.branch 38 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-1)),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.branch 43 (.branch 25 (.leaf (-32)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 51 (.leaf (-6)) (.leaf (-3)))]
def witnessP9_312_6060 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (4)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (6)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (8)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (5)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (4)) (.branch 34 (.leaf (0)) (.leaf (7)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (3)) (.leaf (0)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (6)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (8)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_6060
  counts := ![(.branch 24 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 46 (.branch 42 (.leaf (11)) (.leaf (12))) (.branch 50 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 30 (.leaf (-18)) (.leaf (-21)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-12))) (.branch 14 (.leaf (-14)) (.branch 40 (.leaf (-18)) (.leaf (-20))))),
  (.branch 21 (.branch 13 (.leaf (0)) (.branch 17 (.leaf (-3)) (.leaf (-5)))) (.branch 43 (.branch 39 (.leaf (-7)) (.leaf (-9))) (.branch 47 (.leaf (-11)) (.leaf (-13))))),
  (.branch 7 (.leaf (0)) (.branch 41 (.leaf (-21)) (.leaf (-23)))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 18 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 39 (.branch 31 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19)))) (.branch 47 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 51 (.leaf (-16)) (.leaf (-11))))),
  (.branch 50 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 51 (.leaf (-14)) (.leaf (-9)))),
  (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-10))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-4)) (.leaf (-1))))),
  (.branch 46 (.branch 43 (.branch 42 (.leaf (-23)) (.leaf (-21))) (.branch 44 (.leaf (-19)) (.branch 45 (.leaf (-17)) (.leaf (-15))))) (.branch 49 (.branch 47 (.leaf (-13)) (.branch 48 (.leaf (-11)) (.leaf (-9)))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 16 (.leaf (-5)) (.branch 34 (.leaf (-4)) (.leaf (-3)))),
  (.branch 40 (.branch 34 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_312_6061 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (7)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (0)) (.leaf (5)))) (.branch 17 (.leaf (8)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (6)) (.leaf (7))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (5)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (3))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (8)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (6)) (.branch 41 (.leaf (0)) (.leaf (5)))) (.branch 43 (.leaf (7)) (.branch 44 (.leaf (0)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (0))) (.branch 51 (.leaf (6)) (.leaf (8))))))))
  code := certificateP9_6061
  counts := ![(.branch 24 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 44 (.branch 41 (.leaf (14)) (.leaf (15))) (.branch 47 (.leaf (16)) (.branch 50 (.leaf (17)) (.leaf (18))))))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-17)) (.leaf (-23)))),
  (.branch 2 (.leaf (0)) (.leaf (-20))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-13)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 25 (.leaf (0)) (.branch 51 (.leaf (-3)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.leaf (-28))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 42 (.branch 36 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21)))) (.branch 48 (.branch 45 (.leaf (-20)) (.leaf (-19))) (.branch 51 (.leaf (-18)) (.leaf (-9))))),
  (.branch 48 (.branch 38 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 49 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-5)),
  (.branch 47 (.branch 44 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 35 (.leaf (-2)) (.leaf (0)))]
def witnessP9_312_6062 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (3)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (8)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (7)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (5)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (8))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (4)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (6))) (.branch 38 (.leaf (3)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (7)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (5)) (.branch 44 (.leaf (2)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (0)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (8)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (6))))))))
  code := certificateP9_6062
  counts := ![(.branch 24 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 39 (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.branch 36 (.leaf (12)) (.leaf (13))))) (.branch 45 (.branch 42 (.leaf (14)) (.leaf (15))) (.branch 47 (.leaf (16)) (.branch 50 (.leaf (17)) (.leaf (18))))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 21 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.branch 37 (.leaf (-3)) (.leaf (-5)))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (-34))) (.branch 40 (.leaf (-35)) (.leaf (-36)))),
  (.branch 14 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 48 (.leaf (-19)) (.branch 51 (.leaf (-18)) (.leaf (-9)))),
  (.branch 49 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.branch 44 (.branch 30 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3)))) (.branch 41 (.leaf (-2)) (.branch 42 (.leaf (-1)) (.leaf (0))))),
  (.branch 46 (.branch 43 (.branch 41 (.leaf (-36)) (.branch 42 (.leaf (-33)) (.leaf (-30)))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 50 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))]
def witnessP9_312_6063 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (7)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (5)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (6)) (.branch 21 (.leaf (0)) (.leaf (7)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (5)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (8)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (6)) (.branch 34 (.leaf (0)) (.leaf (3)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (4)) (.leaf (7)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (5)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (6)) (.branch 47 (.leaf (0)) (.leaf (8)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (4)) (.leaf (3))))))))
  code := certificateP9_6063
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-20)) (.leaf (-22)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (-37))) (.branch 39 (.leaf (-38)) (.leaf (-39)))),
  (.branch 13 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 44 (.leaf (-10)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 48 (.branch 46 (.branch 37 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-39)) (.branch 41 (.leaf (-36)) (.leaf (-33)))) (.branch 43 (.leaf (-30)) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_312_6064 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (8)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (4))) (.branch 12 (.leaf (6)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (7)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (4))) (.branch 25 (.leaf (8)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (6)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (3))))) (.branch 35 (.branch 33 (.leaf (7)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (8)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (6)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (4))) (.branch 51 (.leaf (7)) (.leaf (3))))))))
  code := certificateP9_6064
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-43)) (.leaf (-44)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (-16))) (.branch 46 (.leaf (-17)) (.leaf (-18)))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-31)))]
  high := ![(.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 46 (.leaf (-1)) (.leaf (0))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.branch 40 (.branch 21 (.leaf (-44)) (.branch 39 (.leaf (-42)) (.leaf (-39)))) (.branch 42 (.branch 41 (.leaf (-36)) (.leaf (-33))) (.branch 43 (.leaf (-30)) (.leaf (-27))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-24)) (.leaf (-21))) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.leaf (-5)) (.leaf (-3))),
  (.branch 46 (.branch 43 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))))]
def witnessP9_312_6065 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (6)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (5)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (7))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (0)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (8))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (5)))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (0)) (.leaf (7))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (6)))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (0))) (.branch 38 (.leaf (2)) (.leaf (8)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (3)) (.leaf (5)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (7))))) (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (0)) (.leaf (6)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (8))))))))
  code := certificateP9_6065
  counts := ![(.branch 24 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 31 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 2 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 43 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (-42))) (.branch 43 (.leaf (-44)) (.leaf (-45)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-17)) (.leaf (-19)))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (-2))) (.branch 30 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-32))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 41 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-45)) (.leaf (-40))) (.branch 46 (.leaf (-35)) (.leaf (-30)))) (.branch 49 (.branch 48 (.leaf (-25)) (.leaf (-20))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 39 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 31 (.leaf (-6)) (.leaf (-5))),
  (.branch 48 (.branch 26 (.branch 5 (.leaf (-32)) (.leaf (-31))) (.branch 47 (.leaf (-30)) (.leaf (-25)))) (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessP9_312_6066 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (7)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (6)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (5))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (3)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (4)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (8)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (5))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (4)) (.leaf (3))))))))
  code := certificateP9_6066
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-9)) (.leaf (-10)))),
  (.branch 23 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-7)))) (.branch 36 (.leaf (-8)) (.branch 49 (.leaf (-9)) (.leaf (-10))))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 16 (.leaf (0)) (.leaf (-36))),
  (.branch 42 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 44 (.leaf (-10)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 50 (.leaf (-10)) (.branch 51 (.leaf (-8)) (.leaf (-6)))),
  (.branch 49 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 34 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 25 (.branch 20 (.branch 18 (.branch 17 (.leaf (-36)) (.leaf (-35))) (.branch 19 (.leaf (-34)) (.leaf (-33)))) (.branch 22 (.branch 21 (.leaf (-32)) (.leaf (-31))) (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-27)) (.leaf (-26))) (.branch 28 (.leaf (-25)) (.leaf (-24)))) (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))))) (.branch 43 (.branch 38 (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_312_6067 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (8)) (.leaf (6)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (7))) (.branch 25 (.leaf (0)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (6)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (8))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (5)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (7)) (.leaf (6)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (5)) (.leaf (8))) (.branch 51 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_6067
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 33 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14))))) (.branch 46 (.branch 40 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17)))) (.branch 48 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20))))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-20)) (.leaf (-21)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 6 (.leaf (0)) (.leaf (-34))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 41 (.leaf (-8)) (.branch 49 (.leaf (-7)) (.leaf (-5)))),
  (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.branch 43 (.branch 7 (.leaf (-34)) (.branch 42 (.leaf (-33)) (.leaf (-30)))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 33 (.leaf (-8)) (.branch 51 (.leaf (-6)) (.leaf (-3))))]
def witnessP9_312_6068 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (7)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (6)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (5)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (2)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (8)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (4)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6068
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-9)) (.leaf (-10)))),
  (.branch 23 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-7)))) (.branch 36 (.leaf (-8)) (.branch 49 (.leaf (-9)) (.leaf (-10))))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-13)))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (-25)) (.leaf (-26)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 16 (.leaf (0)) (.leaf (-36))),
  (.branch 42 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 44 (.leaf (-10)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 50 (.leaf (-10)) (.branch 51 (.leaf (-8)) (.leaf (-6)))),
  (.leaf (-2)),
  (.branch 49 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 47 (.branch 45 (.branch 27 (.leaf (-26)) (.leaf (-24))) (.branch 46 (.leaf (-21)) (.leaf (-18)))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (0)),
  (.branch 40 (.branch 34 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 25 (.branch 20 (.branch 18 (.branch 17 (.leaf (-36)) (.leaf (-35))) (.branch 19 (.leaf (-34)) (.leaf (-33)))) (.branch 22 (.branch 21 (.leaf (-32)) (.leaf (-31))) (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-27)) (.leaf (-26))) (.branch 28 (.leaf (-25)) (.leaf (-24)))) (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))))) (.branch 43 (.branch 38 (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_312_6069 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (7)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (5)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (2)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (6)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (3))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (5)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (4))) (.branch 38 (.leaf (1)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (8)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (5)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (4))) (.branch 51 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_6069
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 17 (.leaf (-18)) (.branch 22 (.leaf (-19)) (.leaf (-20))))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 16 (.leaf (0)) (.leaf (-36))),
  (.branch 42 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 50 (.branch 45 (.leaf (-11)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 36 (.leaf (-7)) (.leaf (-5))),
  (.branch 46 (.leaf (-1)) (.leaf (0))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 34 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 25 (.branch 20 (.branch 18 (.branch 17 (.leaf (-36)) (.leaf (-35))) (.branch 19 (.leaf (-34)) (.leaf (-33)))) (.branch 22 (.branch 21 (.leaf (-32)) (.leaf (-31))) (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-27)) (.leaf (-26))) (.branch 28 (.leaf (-25)) (.leaf (-24)))) (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))))) (.branch 43 (.branch 38 (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_312_6070 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (7)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (6)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (8)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (3)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (6)))) (.branch 30 (.leaf (4)) (.branch 31 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (7)) (.leaf (3)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (5))) (.branch 38 (.leaf (1)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (4)) (.leaf (6)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (8)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_6070
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 17 (.leaf (-18)) (.branch 22 (.leaf (-19)) (.leaf (-20))))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 35 (.leaf (-32)) (.leaf (-33)))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 50 (.branch 45 (.leaf (-11)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 46 (.leaf (-1)) (.leaf (0))),
  (.branch 48 (.branch 36 (.leaf (-33)) (.branch 47 (.leaf (-30)) (.leaf (-25)))) (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 10 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 43 (.branch 38 (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_312_6071 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (7)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (2)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (8)) (.leaf (6))) (.branch 12 (.leaf (3)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (5)) (.leaf (4)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (7))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (1))) (.branch 25 (.leaf (6)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (8)))) (.branch 30 (.leaf (4)) (.branch 31 (.leaf (1)) (.leaf (5))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (7)) (.leaf (6))) (.branch 38 (.leaf (4)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (5)) (.leaf (3)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (4)) (.leaf (8))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (5)) (.leaf (2))) (.branch 51 (.leaf (6)) (.leaf (4))))))))
  code := certificateP9_6071
  counts := ![(.branch 21 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.leaf (7))))),
  (.branch 26 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-12)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-38))) (.branch 31 (.leaf (-41)) (.leaf (-43)))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 48 (.leaf (-15)) (.leaf (-17)))),
  (.branch 22 (.leaf (0)) (.branch 44 (.leaf (-3)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-15))) (.branch 36 (.leaf (-17)) (.leaf (-18)))),
  (.branch 10 (.leaf (0)) (.branch 45 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 48 (.branch 34 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 48 (.branch 32 (.leaf (-43)) (.branch 47 (.leaf (-42)) (.leaf (-35)))) (.branch 50 (.branch 49 (.leaf (-28)) (.leaf (-21))) (.branch 51 (.leaf (-14)) (.leaf (-7))))),
  (.branch 21 (.branch 6 (.leaf (-17)) (.leaf (-16))) (.branch 36 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-7))))),
  (.branch 50 (.branch 49 (.leaf (-17)) (.leaf (-14))) (.branch 51 (.leaf (-11)) (.leaf (-8)))),
  (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-3)) (.leaf (0)))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-14)) (.leaf (-13))) (.branch 43 (.leaf (-12)) (.leaf (-11))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.leaf (-7)))) (.branch 50 (.branch 49 (.leaf (-6)) (.leaf (-5))) (.branch 51 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 48 (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7)))) (.branch 50 (.branch 49 (.leaf (-6)) (.leaf (-5))) (.branch 51 (.leaf (-4)) (.leaf (-3)))))]
def witnessP9_312_6072 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (7)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (8)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (7)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (4))) (.branch 25 (.leaf (3)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (8)))) (.branch 30 (.leaf (5)) (.branch 31 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (3)) (.branch 34 (.leaf (1)) (.leaf (4)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (0))) (.branch 38 (.leaf (7)) (.leaf (6)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (5)) (.branch 41 (.leaf (1)) (.leaf (3)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (4))))) (.branch 48 (.branch 46 (.leaf (8)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (5))) (.branch 51 (.leaf (3)) (.leaf (6))))))))
  code := certificateP9_6072
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 45 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-21))) (.branch 11 (.leaf (-22)) (.leaf (-23)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-2)) (.leaf (-4)))) (.branch 36 (.leaf (-5)) (.branch 49 (.leaf (-6)) (.leaf (-7))))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (-32))) (.branch 24 (.leaf (-34)) (.leaf (-36)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (-7))) (.branch 50 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-43)) (.leaf (-44)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (-16))) (.branch 46 (.leaf (-17)) (.leaf (-18))))]
  high := ![(.branch 49 (.branch 38 (.leaf (-23)) (.leaf (-20))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))),
  (.branch 34 (.leaf (-5)) (.branch 43 (.leaf (-4)) (.leaf (-3)))),
  (.branch 48 (.branch 46 (.branch 25 (.leaf (-36)) (.leaf (-35))) (.branch 47 (.leaf (-30)) (.leaf (-25)))) (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 51 (.leaf (-10)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 44 (.branch 40 (.branch 21 (.leaf (-44)) (.branch 39 (.leaf (-42)) (.leaf (-39)))) (.branch 42 (.branch 41 (.leaf (-36)) (.leaf (-33))) (.branch 43 (.leaf (-30)) (.leaf (-27))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-24)) (.leaf (-21))) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_312_6073 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (8)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (4)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (6)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (7))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (5)) (.branch 15 (.leaf (2)) (.leaf (8)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (6)) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (7))) (.branch 25 (.leaf (5)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (8)))) (.branch 30 (.leaf (6)) (.branch 31 (.leaf (4)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (5)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (7))) (.branch 38 (.leaf (0)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (6)) (.branch 41 (.leaf (2)) (.leaf (8)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (5)) (.branch 47 (.leaf (4)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (7))) (.branch 51 (.leaf (6)) (.leaf (3))))))))
  code := certificateP9_6073
  counts := ![(.branch 22 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 27 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-21))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-20)) (.leaf (-22)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-8)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2)))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 21 (.leaf (-5)) (.branch 47 (.leaf (-6)) (.leaf (-7))))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-32)) (.leaf (-34)))),
  (.branch 9 (.leaf (0)) (.branch 40 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 49 (.branch 28 (.leaf (-21)) (.leaf (-20))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 48 (.branch 46 (.branch 37 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 35 (.leaf (-2)) (.branch 45 (.leaf (-1)) (.leaf (0)))),
  (.branch 49 (.branch 48 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3))))),
  (.branch 48 (.branch 36 (.branch 15 (.leaf (-34)) (.leaf (-33))) (.branch 47 (.leaf (-30)) (.leaf (-25)))) (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 41 (.leaf (-8)) (.leaf (-5))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_312_6074 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (0)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (0)))) (.branch 17 (.leaf (6)) (.branch 18 (.leaf (1)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (7)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (1)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (0)))) (.branch 30 (.leaf (8)) (.branch 31 (.leaf (1)) (.leaf (3))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (4)) (.leaf (6)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (1)) (.leaf (7)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (3)) (.leaf (0)))) (.branch 43 (.leaf (5)) (.branch 44 (.leaf (1)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (8)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (1)) (.leaf (6))))))))
  code := certificateP9_6074
  counts := ![(.branch 23 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 29 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 42 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 49 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 16 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-11)))) (.branch 29 (.leaf (-12)) (.branch 42 (.leaf (-13)) (.leaf (-14))))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-20)) (.leaf (-21)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (-25))) (.branch 43 (.leaf (-26)) (.leaf (-27)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-40))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (-13)) (.leaf (-14))))]
  high := ![(.branch 50 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 51 (.leaf (-10)) (.leaf (-7)))),
  (.branch 45 (.leaf (-3)) (.leaf (-2))),
  (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 42 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-27)) (.leaf (-24))) (.branch 46 (.leaf (-21)) (.leaf (-18)))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 45 (.branch 41 (.branch 5 (.leaf (-40)) (.branch 40 (.leaf (-39)) (.leaf (-36)))) (.branch 43 (.branch 42 (.leaf (-33)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 31 (.leaf (-14)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_312_6075 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (7)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (2)) (.leaf (0)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (8))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (7))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (1)))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (0)) (.leaf (6))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (8)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (5)) (.branch 41 (.leaf (2)) (.leaf (0)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (1)) (.leaf (7))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (6)) (.leaf (0))) (.branch 51 (.leaf (4)) (.leaf (8))))))))
  code := certificateP9_6075
  counts := ![(.branch 24 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 46 (.branch 42 (.leaf (11)) (.leaf (12))) (.branch 50 (.leaf (13)) (.leaf (14)))))),
  (.branch 22 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 29 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 34 (.leaf (-13)) (.leaf (-14)))),
  (.branch 22 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 11 (.leaf (-5)) (.leaf (-7)))) (.branch 37 (.branch 33 (.leaf (-8)) (.leaf (-9))) (.branch 48 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (-34))) (.branch 40 (.leaf (-35)) (.leaf (-36)))),
  (.branch 14 (.leaf (0)) (.leaf (-10))),
  (.branch 10 (.leaf (0)) (.branch 26 (.leaf (-8)) (.leaf (-10)))),
  (.leaf (0))]
  high := ![(.branch 43 (.branch 35 (.leaf (-14)) (.branch 39 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.leaf (-11)) (.branch 51 (.leaf (-10)) (.leaf (-6))))),
  (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9)))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 46 (.branch 43 (.branch 41 (.leaf (-36)) (.branch 42 (.leaf (-33)) (.leaf (-30)))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 50 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 48 (.branch 46 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.leaf (-7)))) (.branch 50 (.branch 49 (.leaf (-6)) (.leaf (-5))) (.branch 51 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (0))]
def witnessP9_312_6076 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (1)))) (.branch 17 (.leaf (6)) (.branch 18 (.leaf (0)) (.leaf (8))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (1)))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (0)) (.leaf (7))))) (.branch 35 (.branch 33 (.leaf (4)) (.branch 34 (.leaf (0)) (.leaf (6)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (2))) (.branch 38 (.leaf (0)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (4)) (.leaf (1)))) (.branch 43 (.leaf (5)) (.branch 44 (.leaf (0)) (.leaf (8))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (4))) (.branch 51 (.leaf (0)) (.leaf (6))))))))
  code := certificateP9_6076
  counts := ![(.branch 25 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 51 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 27 (.leaf (-8)) (.branch 40 (.leaf (-9)) (.leaf (-10))))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-20))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-7)))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (-25))) (.branch 43 (.leaf (-26)) (.leaf (-27)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 41 (.leaf (-10)) (.branch 48 (.leaf (-9)) (.leaf (-7)))),
  (.branch 50 (.branch 43 (.leaf (-7)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.branch 38 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 49 (.branch 31 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 42 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-27)) (.leaf (-24))) (.branch 46 (.leaf (-21)) (.leaf (-18)))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_312_6077 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (0)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (7)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (1)))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (6)) (.branch 34 (.leaf (2)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (0))) (.branch 38 (.leaf (4)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (2)) (.leaf (0)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (4)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (8)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (4)) (.leaf (5))))))))
  code := certificateP9_6077
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 42 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 46 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-21))) (.branch 11 (.leaf (-22)) (.branch 16 (.leaf (-23)) (.leaf (-24))))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-32))),
  (.branch 46 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 49 (.branch 43 (.leaf (-24)) (.leaf (-20))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 30 (.leaf (-11)) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 45 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 28 (.branch 24 (.branch 22 (.branch 21 (.leaf (-32)) (.leaf (-31))) (.branch 23 (.leaf (-30)) (.leaf (-29)))) (.branch 26 (.branch 25 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.leaf (-25))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-24)) (.leaf (-23))) (.branch 31 (.leaf (-22)) (.leaf (-21)))) (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-17)))))) (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_312_6078 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (7)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (6)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (3)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (8)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (0)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (6)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (1)))) (.branch 30 (.leaf (4)) (.branch 31 (.leaf (7)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (2)) (.branch 34 (.leaf (1)) (.leaf (5)))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (0))) (.branch 38 (.leaf (6)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (4)) (.leaf (0)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (8)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (0)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (1))) (.branch 51 (.leaf (6)) (.leaf (4))))))))
  code := certificateP9_6078
  counts := ![(.branch 21 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 42 (.leaf (8)) (.branch 47 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (-21)) (.leaf (-22)))) (.branch 16 (.leaf (-23)) (.branch 21 (.leaf (-24)) (.leaf (-25))))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 17 (.leaf (-14)) (.branch 43 (.leaf (-16)) (.leaf (-17))))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (-1))) (.branch 30 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 49 (.branch 48 (.leaf (-25)) (.leaf (-20))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 35 (.leaf (-12)) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 50 (.branch 44 (.leaf (-17)) (.leaf (-14))) (.branch 51 (.leaf (-10)) (.leaf (-6)))),
  (.branch 49 (.branch 47 (.leaf (-13)) (.branch 48 (.leaf (-11)) (.leaf (-9)))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-5)) (.leaf (-3))))),
  (.branch 31 (.leaf (-3)) (.branch 42 (.leaf (-2)) (.leaf (0)))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_312_6079 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (7)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (5)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (8)) (.branch 15 (.leaf (2)) (.leaf (4)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (6)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (7)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (4)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (8)) (.leaf (6))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (1))) (.branch 38 (.leaf (5)) (.leaf (7)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (3)) (.leaf (2)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (4)) (.leaf (6))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (8)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (5)) (.leaf (4))))))))
  code := certificateP9_6079
  counts := ![(.branch 20 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 29 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.leaf (7))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 13 (.leaf (-12)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.leaf (-18))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-14))) (.branch 21 (.leaf (-15)) (.branch 47 (.leaf (-17)) (.leaf (-19))))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-24)) (.leaf (-27)))),
  (.branch 29 (.leaf (0)) (.branch 36 (.leaf (-11)) (.leaf (-15)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-8)))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (-37))) (.branch 39 (.leaf (-38)) (.leaf (-39)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (-10))) (.branch 48 (.leaf (-11)) (.leaf (-12))))]
  high := ![(.branch 48 (.branch 14 (.leaf (-13)) (.branch 47 (.leaf (-12)) (.leaf (-10)))) (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.branch 4 (.leaf (-18)) (.leaf (-17))) (.branch 44 (.leaf (-16)) (.branch 51 (.leaf (-14)) (.leaf (-9))))),
  (.branch 49 (.branch 48 (.leaf (-19)) (.leaf (-16))) (.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-10)) (.leaf (-7))))),
  (.branch 42 (.branch 12 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25)))) (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-14)) (.leaf (-7))))),
  (.branch 45 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-4)) (.leaf (0))))),
  (.leaf (-1)),
  (.branch 48 (.branch 46 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-39)) (.branch 41 (.leaf (-36)) (.leaf (-33)))) (.branch 43 (.leaf (-30)) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))]
def witnessP9_312_6080 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (8))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (2)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (3)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (7))) (.branch 25 (.leaf (2)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (3)) (.leaf (1)))) (.branch 30 (.leaf (5)) (.branch 31 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (6)) (.branch 34 (.leaf (4)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (8))) (.branch 38 (.leaf (0)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (2)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (4)) (.branch 44 (.leaf (3)) (.leaf (6))))) (.branch 48 (.branch 46 (.leaf (5)) (.branch 47 (.leaf (2)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (7))) (.branch 51 (.leaf (3)) (.leaf (4))))))))
  code := certificateP9_6080
  counts := ![(.branch 23 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 27 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 42 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.leaf (7))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 16 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))) (.branch 31 (.branch 27 (.leaf (-8)) (.leaf (-9))) (.branch 42 (.leaf (-11)) (.leaf (-12))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 15 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 46 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 24 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 50 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9)))),
  (.branch 49 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-9))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-5)) (.leaf (-3))))),
  (.branch 29 (.leaf (-4)) (.leaf (-3))),
  (.branch 35 (.leaf (-2)) (.branch 44 (.leaf (-1)) (.leaf (0)))),
  (.branch 49 (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3))))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_312_6081 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (1)))) (.branch 17 (.leaf (6)) (.branch 18 (.leaf (0)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (7)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (1)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (1)))) (.branch 30 (.leaf (8)) (.branch 31 (.leaf (0)) (.leaf (3))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (6)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (4))) (.branch 38 (.leaf (1)) (.leaf (7)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (3)) (.leaf (1)))) (.branch 43 (.leaf (5)) (.branch 44 (.leaf (0)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (8)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (1)) (.leaf (6))))))))
  code := certificateP9_6081
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-20)) (.leaf (-22)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-28))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-40)) (.leaf (-41)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (-13))) (.branch 47 (.leaf (-14)) (.leaf (-15))))]
  high := ![(.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 47 (.leaf (-5)) (.leaf (-3))),
  (.branch 48 (.branch 46 (.branch 37 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.branch 44 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 35 (.leaf (-2)) (.leaf (0))),
  (.branch 45 (.branch 41 (.branch 22 (.leaf (-41)) (.branch 40 (.leaf (-39)) (.leaf (-36)))) (.branch 43 (.branch 42 (.leaf (-33)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_312_6082 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (7)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (4)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (8)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (4)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (5)) (.leaf (0))) (.branch 38 (.leaf (3)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (4)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (6)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (5)) (.leaf (0))) (.branch 51 (.leaf (4)) (.leaf (1))))))))
  code := certificateP9_6082
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-4)))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 18 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-47))),
  (.branch 31 (.leaf (0)) (.leaf (-21)))]
  high := ![(.branch 47 (.leaf (-11)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 46 (.leaf (-1)) (.leaf (0))),
  (.branch 49 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 48 (.branch 30 (.leaf (-17)) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 43 (.leaf (-4)) (.leaf (-3))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 16 (.branch 10 (.branch 7 (.branch 6 (.leaf (-47)) (.leaf (-46))) (.branch 8 (.leaf (-45)) (.branch 9 (.leaf (-44)) (.leaf (-43))))) (.branch 13 (.branch 11 (.leaf (-42)) (.branch 12 (.leaf (-41)) (.leaf (-40)))) (.branch 14 (.leaf (-39)) (.branch 15 (.leaf (-38)) (.leaf (-37)))))) (.branch 22 (.branch 19 (.branch 17 (.leaf (-36)) (.branch 18 (.leaf (-35)) (.leaf (-34)))) (.branch 20 (.leaf (-33)) (.branch 21 (.leaf (-32)) (.leaf (-31))))) (.branch 25 (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))) (.branch 26 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25))))))) (.branch 40 (.branch 34 (.branch 31 (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-22)))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_312_6083 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (7)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (6)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (8)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (7)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (6)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (0))) (.branch 38 (.leaf (3)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (5)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (8)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (0))) (.branch 51 (.leaf (6)) (.leaf (1))))))))
  code := certificateP9_6083
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (-28))) (.branch 42 (.leaf (-29)) (.leaf (-30)))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 47 (.leaf (-11)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 46 (.leaf (-1)) (.leaf (0))),
  (.branch 49 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 48 (.branch 30 (.leaf (-17)) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-30)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 17 (.leaf (-4)) (.leaf (-3))),
  (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_312_6084 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (5)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (2))) (.branch 25 (.leaf (6)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (4)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (2))) (.branch 38 (.leaf (7)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (3)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (2))) (.branch 51 (.leaf (8)) (.leaf (1))))))))
  code := certificateP9_6084
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1))),
  (.branch 51 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-40))),
  (.branch 25 (.leaf (0)) (.leaf (-27))),
  (.branch 38 (.leaf (0)) (.leaf (-14))),
  (.branch 51 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 48 (.leaf (-2)) (.leaf (0))),
  (.branch 46 (.leaf (-8)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 50 (.branch 43 (.leaf (-7)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 22 (.branch 17 (.branch 14 (.branch 13 (.leaf (-40)) (.leaf (-39))) (.branch 15 (.leaf (-38)) (.branch 16 (.leaf (-37)) (.leaf (-36))))) (.branch 19 (.branch 18 (.leaf (-35)) (.leaf (-34))) (.branch 20 (.leaf (-33)) (.branch 21 (.leaf (-32)) (.leaf (-31)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-30)) (.leaf (-29))) (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26))))) (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-21))))))) (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25)))) (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-22))))) (.branch 34 (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19)))) (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))))) (.branch 45 (.branch 41 (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 41 (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_312_6085 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (2))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (5)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (7)) (.leaf (2))) (.branch 25 (.leaf (4)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (5)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (6)) (.leaf (2))) (.branch 38 (.leaf (3)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (4)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (8)) (.leaf (2))) (.branch 51 (.leaf (5)) (.leaf (1))))))))
  code := certificateP9_6085
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-4)) (.leaf (-5)))),
  (.branch 10 (.leaf (0)) (.leaf (-16))),
  (.branch 23 (.leaf (0)) (.leaf (-29))),
  (.branch 49 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 48 (.leaf (-2)) (.leaf (0))),
  (.branch 46 (.leaf (-8)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 46 (.branch 43 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 34 (.leaf (-5)) (.leaf (-3))),
  (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 30 (.branch 26 (.branch 24 (.leaf (-29)) (.branch 25 (.leaf (-28)) (.leaf (-27)))) (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-25))) (.branch 29 (.leaf (-24)) (.leaf (-23))))) (.branch 33 (.branch 31 (.leaf (-22)) (.branch 32 (.leaf (-21)) (.leaf (-20)))) (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_312_6086 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (7)) (.leaf (2))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (4)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (2))) (.branch 25 (.leaf (4)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (4)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (8)) (.leaf (2))) (.branch 38 (.leaf (3)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (4)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (6)) (.leaf (2))) (.branch 51 (.leaf (4)) (.leaf (1))))))))
  code := certificateP9_6086
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 23 (.leaf (0)) (.leaf (-29))),
  (.branch 49 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-42))),
  (.branch 36 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 48 (.leaf (-2)) (.leaf (0))),
  (.branch 46 (.leaf (-8)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.leaf (-5)) (.branch 43 (.leaf (-4)) (.leaf (-3)))),
  (.branch 37 (.branch 30 (.branch 26 (.branch 24 (.leaf (-29)) (.branch 25 (.leaf (-28)) (.leaf (-27)))) (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-25))) (.branch 29 (.leaf (-24)) (.leaf (-23))))) (.branch 33 (.branch 31 (.leaf (-22)) (.branch 32 (.leaf (-21)) (.leaf (-20)))) (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 20 (.branch 15 (.branch 12 (.branch 11 (.leaf (-42)) (.leaf (-41))) (.branch 13 (.leaf (-40)) (.branch 14 (.leaf (-39)) (.leaf (-38))))) (.branch 17 (.branch 16 (.leaf (-37)) (.leaf (-36))) (.branch 18 (.leaf (-35)) (.branch 19 (.leaf (-34)) (.leaf (-33)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-32)) (.leaf (-31))) (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28))))) (.branch 28 (.branch 26 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25)))) (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-22))))))) (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_312_6087 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (2))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (6)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (2))) (.branch 25 (.leaf (5)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (7)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (2))) (.branch 38 (.leaf (3)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (5)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (2))) (.branch 51 (.leaf (8)) (.leaf (1))))))))
  code := certificateP9_6087
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1))),
  (.branch 51 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 16 (.leaf (0)) (.leaf (-36))),
  (.branch 33 (.leaf (0)) (.leaf (-19))),
  (.branch 51 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 48 (.leaf (-2)) (.leaf (0))),
  (.branch 46 (.leaf (-8)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 43 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 34 (.branch 25 (.branch 20 (.branch 18 (.branch 17 (.leaf (-36)) (.leaf (-35))) (.branch 19 (.leaf (-34)) (.leaf (-33)))) (.branch 22 (.branch 21 (.leaf (-32)) (.leaf (-31))) (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-27)) (.leaf (-26))) (.branch 28 (.leaf (-25)) (.leaf (-24)))) (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))))) (.branch 43 (.branch 38 (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_312_6088 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (8)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (6)) (.leaf (1))) (.branch 25 (.leaf (7)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (5)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (8)) (.branch 34 (.leaf (2)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (6)) (.leaf (0))) (.branch 38 (.leaf (3)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (2)) (.leaf (7)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (5)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (6)) (.leaf (1))) (.branch 51 (.leaf (8)) (.leaf (4))))))))
  code := certificateP9_6088
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-21))) (.branch 11 (.leaf (-22)) (.leaf (-23)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))) (.branch 19 (.leaf (-8)) (.branch 24 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 49 (.branch 38 (.leaf (-23)) (.leaf (-20))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 51 (.leaf (-10)) (.leaf (-5))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 43 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 34 (.leaf (-5)) (.leaf (-3)))]
def witnessP9_312_6089 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (5)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (4)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (8)) (.branch 18 (.leaf (5)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (2)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (7)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (1)) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (5)) (.leaf (8))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (2)) (.leaf (7)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (4)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (6)) (.branch 41 (.leaf (2)) (.leaf (0)))) (.branch 43 (.leaf (8)) (.branch 44 (.leaf (5)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (7)) (.leaf (1))) (.branch 51 (.leaf (4)) (.leaf (6))))))))
  code := certificateP9_6089
  counts := ![(.branch 24 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 48 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 45 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 24 (.leaf (-43)) (.leaf (-44)))),
  (.branch 27 (.branch 4 (.leaf (0)) (.leaf (-16))) (.branch 50 (.leaf (-17)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-19)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-8))) (.branch 43 (.leaf (-11)) (.leaf (-13))))]
  high := ![(.branch 43 (.branch 31 (.branch 25 (.leaf (-44)) (.leaf (-42))) (.branch 37 (.leaf (-40)) (.leaf (-38)))) (.branch 50 (.branch 49 (.leaf (-36)) (.leaf (-27))) (.branch 51 (.leaf (-18)) (.leaf (-9))))),
  (.branch 51 (.leaf (-18)) (.leaf (-9))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 48 (.branch 38 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-1)),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 50 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5))))))]
def witnessP9_312_6090 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (7)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (5))) (.branch 12 (.leaf (3)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (8)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (7)) (.leaf (5))) (.branch 25 (.leaf (0)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (1)) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (8)) (.leaf (6))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (2)) (.leaf (4)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (5))) (.branch 38 (.leaf (3)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (7)) (.branch 41 (.leaf (2)) (.leaf (0)))) (.branch 43 (.leaf (4)) (.branch 44 (.leaf (1)) (.leaf (6))))) (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (0)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (8)) (.leaf (5))) (.branch 51 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_6090
  counts := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 51 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 47 (.leaf (-6)) (.leaf (-7)))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 44 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-37))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (-10)) (.leaf (-11))))]
  high := ![(.branch 49 (.branch 48 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3))))),
  (.branch 45 (.leaf (-4)) (.leaf (-3))),
  (.branch 49 (.branch 35 (.leaf (-10)) (.branch 42 (.leaf (-9)) (.leaf (-8)))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 44 (.leaf (-1)) (.leaf (0))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 42 (.branch 6 (.leaf (-37)) (.branch 41 (.leaf (-36)) (.leaf (-33)))) (.branch 43 (.leaf (-30)) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 50 (.branch 32 (.leaf (-11)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))]
def witnessP9_312_6091 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (7)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (5)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (5)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (4)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (3)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (5)) (.branch 34 (.leaf (2)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (0))) (.branch 38 (.leaf (4)) (.leaf (8)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (2)) (.leaf (5)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (5)) (.leaf (6))))))))
  code := certificateP9_6091
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-21))) (.branch 11 (.leaf (-22)) (.leaf (-23)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))) (.branch 19 (.leaf (-8)) (.branch 24 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-2)) (.leaf (-4)))) (.branch 36 (.leaf (-5)) (.branch 49 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-39))),
  (.branch 39 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 49 (.branch 38 (.leaf (-23)) (.leaf (-20))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 51 (.leaf (-10)) (.leaf (-5))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.leaf (-5)) (.branch 43 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 32 (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-39)) (.leaf (-38))) (.branch 16 (.leaf (-37)) (.leaf (-36)))) (.branch 19 (.branch 18 (.leaf (-35)) (.leaf (-34))) (.branch 20 (.leaf (-33)) (.branch 21 (.leaf (-32)) (.leaf (-31)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-30)) (.leaf (-29))) (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26))))) (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-21))))))) (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_312_6092 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (7)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (6)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (5)) (.leaf (8))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (4)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (3)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (6)) (.branch 34 (.leaf (2)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (0))) (.branch 38 (.leaf (4)) (.leaf (7)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (2)) (.leaf (5)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (6)) (.leaf (8))))))))
  code := certificateP9_6092
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-21))) (.branch 11 (.leaf (-22)) (.leaf (-23)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))) (.branch 19 (.leaf (-8)) (.branch 24 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-2)) (.leaf (-4)))) (.branch 36 (.leaf (-5)) (.branch 49 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-4)) (.leaf (-5)))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 49 (.branch 38 (.leaf (-23)) (.leaf (-20))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 51 (.leaf (-10)) (.leaf (-5))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 46 (.branch 43 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 34 (.leaf (-5)) (.leaf (-3))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_312_6093 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (7)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (6)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (7)) (.leaf (1))) (.branch 25 (.leaf (3)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (6)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (8)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (3)) (.branch 34 (.leaf (2)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (0))) (.branch 38 (.leaf (5)) (.leaf (7)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (2)) (.leaf (3)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (4)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (6)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (8)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (4))))))))
  code := certificateP9_6093
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-21))) (.branch 11 (.leaf (-22)) (.leaf (-23)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))) (.branch 19 (.leaf (-8)) (.branch 24 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 26 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-43)) (.leaf (-44)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (-16))) (.branch 46 (.leaf (-17)) (.leaf (-18)))),
  (.branch 5 (.leaf (0)) (.branch 39 (.leaf (-25)) (.leaf (-27)))),
  (.branch 13 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 49 (.branch 38 (.leaf (-23)) (.leaf (-20))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 51 (.leaf (-10)) (.leaf (-5))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 34 (.leaf (-5)) (.branch 43 (.leaf (-4)) (.leaf (-3)))),
  (.branch 45 (.leaf (-1)) (.leaf (0))),
  (.branch 44 (.branch 40 (.branch 21 (.leaf (-44)) (.branch 39 (.leaf (-42)) (.leaf (-39)))) (.branch 42 (.branch 41 (.leaf (-36)) (.leaf (-33))) (.branch 43 (.leaf (-30)) (.leaf (-27))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-24)) (.leaf (-21))) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-27)) (.branch 41 (.leaf (-25)) (.leaf (-23)))) (.branch 43 (.leaf (-21)) (.branch 44 (.leaf (-19)) (.leaf (-17))))) (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-13)) (.leaf (-11)))) (.branch 50 (.branch 49 (.leaf (-9)) (.leaf (-7))) (.branch 51 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 32 (.branch 14 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-5)) (.leaf (-3)))))]
def witnessP9_312_6094 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 4 (.leaf (8)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (7)) (.leaf (6))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (5)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (8)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (7)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (6))) (.branch 25 (.leaf (2)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (3)) (.leaf (5)))) (.branch 30 (.leaf (8)) (.branch 31 (.leaf (2)) (.leaf (4))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (3)))) (.branch 37 (.branch 36 (.leaf (7)) (.leaf (6))) (.branch 38 (.leaf (1)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (4)) (.leaf (5)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (8)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (7)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (6))) (.branch 51 (.leaf (3)) (.leaf (1))))))))
  code := certificateP9_6094
  counts := ![(.branch 20 (.branch 8 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-11)) (.leaf (-12)))),
  (.branch 12 (.leaf (0)) (.branch 38 (.leaf (-4)) (.leaf (-6)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 31 (.leaf (-12)) (.leaf (-13)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 49 (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-10)) (.leaf (-8)))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 46 (.branch 39 (.leaf (-6)) (.leaf (-5))) (.branch 47 (.leaf (-2)) (.leaf (0)))),
  (.branch 48 (.branch 32 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))) (.branch 50 (.branch 49 (.leaf (-9)) (.leaf (-7))) (.branch 51 (.leaf (-5)) (.leaf (-3))))),
  (.branch 36 (.leaf (-5)) (.branch 44 (.leaf (-4)) (.leaf (-3)))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.branch 45 (.branch 31 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_312_6095 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (6)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (3)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (8)) (.leaf (6)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (7)) (.leaf (5))) (.branch 25 (.leaf (1)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (6)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (3)) (.leaf (8))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (4)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (5))) (.branch 38 (.leaf (0)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (7)) (.leaf (6)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (4)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (3)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (8)) (.leaf (5))) (.branch 51 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_6095
  counts := ![(.branch 22 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 27 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-21))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-6))) (.branch 14 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-20)) (.leaf (-22)))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 21 (.leaf (-5)) (.branch 47 (.leaf (-6)) (.leaf (-7))))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2)))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-34)) (.leaf (-35)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (-7))) (.branch 49 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 49 (.branch 28 (.leaf (-21)) (.leaf (-20))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 41 (.leaf (-8)) (.leaf (-5))),
  (.branch 48 (.branch 46 (.branch 37 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 49 (.branch 48 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3))))),
  (.branch 35 (.leaf (-2)) (.branch 45 (.leaf (-1)) (.leaf (0)))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.branch 43 (.branch 24 (.leaf (-35)) (.branch 42 (.leaf (-33)) (.leaf (-30)))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))]
def witnessP9_312_6096 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (7))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (6)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (8))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (7))) (.branch 25 (.leaf (2)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (4)) (.leaf (1)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (5)) (.leaf (8))))) (.branch 35 (.branch 33 (.leaf (3)) (.branch 34 (.leaf (2)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (6)) (.leaf (7))) (.branch 38 (.leaf (1)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (5)) (.leaf (2)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (8))))) (.branch 48 (.branch 46 (.leaf (6)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (7))) (.branch 51 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6096
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 2 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 44 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-10)))) (.branch 30 (.leaf (-11)) (.branch 43 (.leaf (-12)) (.leaf (-13))))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 33 (.leaf (-42)) (.leaf (-43)))),
  (.branch 7 (.leaf (0)) (.leaf (-17))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-2)) (.leaf (-4)))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (-27))) (.branch 46 (.leaf (-29)) (.leaf (-30)))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 49 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-10)) (.branch 51 (.leaf (-8)) (.leaf (-6))))),
  (.branch 48 (.branch 30 (.leaf (-17)) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 43 (.leaf (-4)) (.leaf (-3))),
  (.branch 47 (.branch 45 (.branch 34 (.leaf (-43)) (.leaf (-40))) (.branch 46 (.leaf (-35)) (.leaf (-30)))) (.branch 49 (.branch 48 (.leaf (-25)) (.leaf (-20))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 29 (.branch 8 (.leaf (-17)) (.leaf (-16))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 21 (.leaf (-4)) (.branch 42 (.leaf (-3)) (.leaf (0)))),
  (.branch 49 (.branch 47 (.leaf (-30)) (.branch 48 (.leaf (-25)) (.leaf (-20)))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_312_6097 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (1)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (7)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (3)) (.leaf (1)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (4))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (6)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (2))) (.branch 38 (.leaf (1)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (4)) (.leaf (1)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (8)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (2))) (.branch 51 (.leaf (1)) (.leaf (5))))))))
  code := certificateP9_6097
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-20)) (.leaf (-22)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-31))),
  (.branch 47 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 47 (.leaf (-5)) (.leaf (-3))),
  (.branch 44 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.branch 46 (.branch 37 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 43 (.branch 38 (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 28 (.branch 24 (.branch 22 (.leaf (-31)) (.branch 23 (.leaf (-30)) (.leaf (-29)))) (.branch 26 (.branch 25 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.leaf (-25))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-24)) (.leaf (-23))) (.branch 31 (.leaf (-22)) (.leaf (-21)))) (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-17)))))) (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_312_6098 : CycleWitness 9 where
  length := 51
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (6)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (1)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (7)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (1)))) (.branch 17 (.leaf (5)) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (8)) (.branch 22 (.leaf (0)) (.leaf (1)))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (1)) (.branch 28 (.leaf (0)) (.leaf (6)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (5)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (7)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (2)) (.leaf (0)))) (.branch 43 (.leaf (4)) (.branch 44 (.leaf (1)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (8)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 49 (.leaf (3)) (.branch 50 (.leaf (1)) (.leaf (5))))))))
  code := certificateP9_6098
  counts := ![(.branch 22 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))) (.branch 36 (.branch 28 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 42 (.branch 39 (.leaf (14)) (.leaf (15))) (.branch 45 (.leaf (16)) (.branch 48 (.leaf (17)) (.leaf (18))))))),
  (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 33 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.leaf (15)))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 19 (.leaf (-4)) (.branch 36 (.leaf (-5)) (.leaf (-6))))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-43)) (.leaf (-44)))),
  (.branch 12 (.leaf (0)) (.leaf (-27))),
  (.branch 21 (.leaf (0)) (.branch 46 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))),
  (.leaf (-5)),
  (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-8)) (.leaf (-7))) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 40 (.branch 34 (.branch 31 (.branch 30 (.leaf (-44)) (.leaf (-42))) (.branch 32 (.leaf (-40)) (.branch 33 (.leaf (-38)) (.leaf (-36))))) (.branch 37 (.branch 35 (.leaf (-34)) (.branch 36 (.leaf (-32)) (.leaf (-30)))) (.branch 38 (.leaf (-28)) (.branch 39 (.leaf (-26)) (.leaf (-24)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-22)) (.leaf (-20))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-16)) (.leaf (-14))))) (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 44 (.branch 40 (.branch 13 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-24)))) (.branch 42 (.branch 41 (.leaf (-22)) (.leaf (-20))) (.branch 43 (.leaf (-18)) (.leaf (-16))))) (.branch 47 (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))))]
def witnessP9_312_6099 : CycleWitness 9 where
  length := 51
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (6)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 11 (.leaf (7)) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (5)) (.leaf (0)))) (.branch 17 (.leaf (3)) (.branch 19 (.leaf (0)) (.leaf (8))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (6)) (.leaf (0)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (5))))) (.branch 36 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (0)))) (.branch 37 (.leaf (7)) (.branch 38 (.leaf (0)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (0)))) (.branch 43 (.leaf (4)) (.branch 44 (.leaf (0)) (.leaf (8))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 49 (.leaf (5)) (.branch 50 (.leaf (0)) (.leaf (3))))))))
  code := certificateP9_6099
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))) (.branch 21 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 23 (.leaf (12)) (.leaf (13)))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (14)) (.branch 29 (.leaf (15)) (.leaf (16)))) (.branch 35 (.branch 33 (.leaf (17)) (.leaf (18))) (.branch 36 (.leaf (19)) (.leaf (20))))) (.branch 44 (.branch 40 (.leaf (21)) (.branch 42 (.leaf (22)) (.leaf (23)))) (.branch 48 (.branch 46 (.leaf (24)) (.leaf (25))) (.branch 50 (.leaf (26)) (.leaf (27))))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-8))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 28 (.leaf (-45)) (.leaf (-46)))),
  (.branch 11 (.leaf (0)) (.leaf (-29))),
  (.branch 20 (.leaf (0)) (.branch 45 (.leaf (-11)) (.leaf (-12))))]
  high := ![(.branch 43 (.branch 39 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 47 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 49 (.leaf (-10)) (.leaf (-9))))),
  (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2)))),
  (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-8)) (.leaf (-7))) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.leaf (-2)) (.leaf (-1))),
  (.branch 39 (.branch 33 (.branch 30 (.branch 29 (.leaf (-46)) (.leaf (-44))) (.branch 31 (.leaf (-42)) (.branch 32 (.leaf (-40)) (.leaf (-38))))) (.branch 36 (.branch 34 (.leaf (-36)) (.branch 35 (.leaf (-34)) (.leaf (-32)))) (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-28)) (.leaf (-26)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-24)) (.branch 41 (.leaf (-22)) (.leaf (-20)))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-16)) (.leaf (-14))))) (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 43 (.branch 39 (.branch 12 (.leaf (-29)) (.branch 38 (.leaf (-28)) (.leaf (-26)))) (.branch 41 (.branch 40 (.leaf (-24)) (.leaf (-22))) (.branch 42 (.leaf (-20)) (.leaf (-18))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-16)) (.leaf (-14))) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))))]
def witnessP9_312_6100 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (6)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (7)) (.leaf (0)))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (8)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (1))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (6))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (5)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (0)) (.leaf (2)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (7)) (.branch 40 (.leaf (0)) (.leaf (4)))) (.branch 42 (.leaf (1)) (.branch 43 (.leaf (0)) (.leaf (2))))) (.branch 47 (.branch 45 (.leaf (3)) (.branch 46 (.leaf (0)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (8)) (.leaf (0))) (.branch 50 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_6100
  counts := ![(.branch 23 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))) (.branch 37 (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 43 (.branch 40 (.leaf (14)) (.leaf (15))) (.branch 46 (.leaf (16)) (.branch 49 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 51 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 38 (.leaf (-3)) (.leaf (-4)))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 16 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-41))),
  (.branch 14 (.leaf (0)) (.branch 39 (.leaf (-23)) (.leaf (-24)))),
  (.branch 22 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 44 (.branch 38 (.leaf (-16)) (.branch 41 (.leaf (-15)) (.leaf (-14)))) (.branch 47 (.leaf (-13)) (.branch 50 (.leaf (-12)) (.leaf (-6))))),
  (.branch 49 (.branch 48 (.leaf (-12)) (.leaf (-9))) (.branch 50 (.leaf (-6)) (.leaf (-3)))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.branch 48 (.leaf (-1)) (.leaf (0))))),
  (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 40 (.branch 35 (.branch 32 (.branch 6 (.leaf (-41)) (.leaf (-40))) (.branch 33 (.leaf (-38)) (.branch 34 (.leaf (-36)) (.leaf (-34))))) (.branch 37 (.branch 36 (.leaf (-32)) (.leaf (-30))) (.branch 38 (.leaf (-28)) (.branch 39 (.leaf (-26)) (.leaf (-24)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-22)) (.leaf (-20))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-16)) (.leaf (-14))))) (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-24)) (.branch 41 (.leaf (-22)) (.leaf (-20)))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-16)) (.leaf (-14))))) (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 49 (.branch 23 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2))))]
def witnessP9_312_6101 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (4)) (.branch 14 (.leaf (0)) (.leaf (6)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (0)) (.leaf (2))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (7)) (.branch 33 (.leaf (0)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (0)) (.leaf (3)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (5)) (.leaf (0)))) (.branch 42 (.leaf (2)) (.branch 43 (.leaf (0)) (.leaf (1))))) (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (3)) (.leaf (4)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (8))) (.branch 50 (.leaf (0)) (.leaf (2))))))))
  code := certificateP9_6101
  counts := ![(.branch 24 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 20 (.leaf (9)) (.branch 22 (.leaf (10)) (.leaf (11)))))) (.branch 37 (.branch 31 (.branch 26 (.leaf (12)) (.branch 28 (.leaf (13)) (.leaf (14)))) (.branch 33 (.leaf (15)) (.branch 35 (.leaf (16)) (.leaf (17))))) (.branch 43 (.branch 39 (.leaf (18)) (.branch 41 (.leaf (19)) (.leaf (20)))) (.branch 48 (.branch 45 (.leaf (21)) (.leaf (22))) (.branch 50 (.leaf (23)) (.leaf (24))))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-10)))) (.branch 9 (.branch 7 (.leaf (-11)) (.leaf (-12))) (.branch 11 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 13 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.leaf (0)) (.leaf (-36))),
  (.branch 32 (.leaf (0)) (.leaf (-19))),
  (.branch 49 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 46 (.leaf (-14)) (.leaf (-8))),
  (.branch 47 (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 43 (.leaf (-1)) (.leaf (0))),
  (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 24 (.branch 19 (.branch 17 (.branch 16 (.leaf (-36)) (.leaf (-35))) (.branch 18 (.leaf (-34)) (.leaf (-33)))) (.branch 21 (.branch 20 (.leaf (-32)) (.leaf (-31))) (.branch 22 (.leaf (-30)) (.branch 23 (.leaf (-29)) (.leaf (-28)))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-27)) (.leaf (-26))) (.branch 27 (.leaf (-25)) (.leaf (-24)))) (.branch 30 (.branch 29 (.leaf (-23)) (.leaf (-22))) (.branch 31 (.leaf (-21)) (.branch 32 (.leaf (-20)) (.leaf (-19))))))) (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-18)) (.leaf (-17))) (.branch 36 (.leaf (-16)) (.leaf (-15)))) (.branch 39 (.branch 38 (.leaf (-14)) (.leaf (-13))) (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 36 (.branch 34 (.branch 33 (.leaf (-19)) (.leaf (-18))) (.branch 35 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_312_6102 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (6)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (3)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (7)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (1))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (8)) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (5)) (.leaf (6)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (0)) (.leaf (4)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 42 (.leaf (1)) (.branch 43 (.leaf (7)) (.leaf (0))))) (.branch 47 (.branch 45 (.leaf (3)) (.branch 46 (.leaf (0)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (2)) (.leaf (0))) (.branch 50 (.leaf (5)) (.leaf (8))))))))
  code := certificateP9_6102
  counts := ![(.branch 24 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 12 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))) (.branch 37 (.branch 29 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.branch 35 (.leaf (14)) (.leaf (15))))) (.branch 44 (.branch 39 (.leaf (16)) (.branch 41 (.leaf (17)) (.leaf (18)))) (.branch 46 (.leaf (19)) (.branch 49 (.leaf (20)) (.leaf (21))))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))) (.branch 24 (.branch 7 (.leaf (-5)) (.leaf (-6))) (.branch 41 (.leaf (-7)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 16 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.branch 34 (.leaf (-33)) (.leaf (-34)))),
  (.branch 17 (.leaf (0)) (.leaf (-17))),
  (.leaf (0))]
  high := ![(.branch 47 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.branch 49 (.branch 48 (.leaf (-12)) (.leaf (-9))) (.branch 50 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))) (.branch 42 (.leaf (-10)) (.branch 43 (.leaf (-9)) (.leaf (-8))))) (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (-34)) (.leaf (-32))) (.branch 37 (.leaf (-30)) (.leaf (-28)))) (.branch 40 (.branch 39 (.leaf (-26)) (.leaf (-24))) (.branch 41 (.leaf (-22)) (.leaf (-20))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-16))) (.branch 45 (.leaf (-14)) (.leaf (-12)))) (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 46 (.branch 44 (.branch 18 (.leaf (-17)) (.leaf (-16))) (.branch 45 (.leaf (-14)) (.leaf (-12)))) (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (0))]
def witnessP9_312_6103 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (7)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (8)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (4))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 29 (.leaf (6)) (.branch 30 (.leaf (3)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (2)) (.branch 33 (.leaf (0)) (.leaf (5)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (0)) (.leaf (7)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 42 (.leaf (4)) (.branch 43 (.leaf (0)) (.leaf (1))))) (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (8)) (.leaf (3)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (2))) (.branch 50 (.leaf (0)) (.leaf (5))))))))
  code := certificateP9_6103
  counts := ![(.branch 24 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 20 (.leaf (9)) (.branch 22 (.leaf (10)) (.leaf (11)))))) (.branch 37 (.branch 31 (.branch 26 (.leaf (12)) (.branch 28 (.leaf (13)) (.leaf (14)))) (.branch 33 (.leaf (15)) (.branch 35 (.leaf (16)) (.leaf (17))))) (.branch 43 (.branch 39 (.leaf (18)) (.branch 41 (.leaf (19)) (.leaf (20)))) (.branch 48 (.branch 45 (.leaf (21)) (.leaf (22))) (.branch 50 (.leaf (23)) (.leaf (24))))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-10)))) (.branch 9 (.branch 7 (.leaf (-11)) (.leaf (-12))) (.branch 11 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 13 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-43)) (.leaf (-44)))),
  (.branch 12 (.leaf (0)) (.leaf (-27))),
  (.branch 21 (.leaf (0)) (.branch 46 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 46 (.leaf (-14)) (.leaf (-8))),
  (.branch 47 (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 41 (.leaf (-5)) (.branch 50 (.leaf (-4)) (.leaf (-2)))),
  (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 40 (.branch 34 (.branch 31 (.branch 30 (.leaf (-44)) (.leaf (-42))) (.branch 32 (.leaf (-40)) (.branch 33 (.leaf (-38)) (.leaf (-36))))) (.branch 37 (.branch 35 (.leaf (-34)) (.branch 36 (.leaf (-32)) (.leaf (-30)))) (.branch 38 (.leaf (-28)) (.branch 39 (.leaf (-26)) (.leaf (-24)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-22)) (.leaf (-20))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-16)) (.leaf (-14))))) (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 44 (.branch 40 (.branch 13 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-24)))) (.branch 42 (.branch 41 (.leaf (-22)) (.leaf (-20))) (.branch 43 (.leaf (-18)) (.leaf (-16))))) (.branch 47 (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))))]
def witnessP9_312_6104 : CycleWitness 9 where
  length := 51
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (5)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (4)) (.leaf (0)))) (.branch 17 (.leaf (6)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (0)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (5)) (.branch 28 (.leaf (0)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (4))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (7)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (3)) (.leaf (0)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (5)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (1)))) (.branch 49 (.leaf (4)) (.branch 50 (.leaf (0)) (.leaf (8))))))))
  code := certificateP9_6104
  counts := ![(.branch 25 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 13 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 23 (.leaf (9)) (.leaf (10)))))) (.branch 38 (.branch 30 (.branch 28 (.leaf (11)) (.leaf (12))) (.branch 33 (.leaf (13)) (.branch 35 (.leaf (14)) (.leaf (15))))) (.branch 45 (.branch 40 (.leaf (16)) (.branch 42 (.leaf (17)) (.leaf (18)))) (.branch 47 (.leaf (19)) (.branch 50 (.leaf (20)) (.leaf (21))))))),
  (.branch 20 (.branch 9 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 51 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-10)) (.leaf (-12)))),
  (.branch 3 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 20 (.leaf (-7)) (.branch 37 (.leaf (-10)) (.leaf (-13))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 29 (.leaf (-6)) (.branch 46 (.leaf (-7)) (.leaf (-8))))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.branch 17 (.leaf (0)) (.leaf (-34))),
  (.branch 34 (.leaf (0)) (.leaf (-17))),
  (.leaf (0))]
  high := ![(.branch 43 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-7)))),
  (.branch 49 (.branch 38 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10)))),
  (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4))))),
  (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (-34)) (.leaf (-33))) (.branch 20 (.leaf (-32)) (.leaf (-31)))) (.branch 23 (.branch 22 (.leaf (-30)) (.leaf (-29))) (.branch 24 (.leaf (-28)) (.leaf (-27))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-26)) (.leaf (-25))) (.branch 28 (.leaf (-24)) (.leaf (-23)))) (.branch 31 (.branch 30 (.leaf (-22)) (.leaf (-21))) (.branch 32 (.leaf (-20)) (.branch 33 (.leaf (-19)) (.leaf (-18))))))) (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (-17)) (.leaf (-16))) (.branch 37 (.leaf (-15)) (.leaf (-14)))) (.branch 40 (.branch 39 (.leaf (-13)) (.leaf (-12))) (.branch 41 (.leaf (-11)) (.leaf (-10))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (-17)) (.leaf (-16))) (.branch 37 (.leaf (-15)) (.leaf (-14)))) (.branch 40 (.branch 39 (.leaf (-13)) (.leaf (-12))) (.branch 41 (.leaf (-11)) (.leaf (-10))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_312_6105 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (3)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (6)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (1))) (.branch 24 (.leaf (3)) (.leaf (0))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (7)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (3)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (5)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (0)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (4)) (.branch 40 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (3)) (.leaf (1))))) (.branch 47 (.branch 45 (.leaf (6)) (.branch 46 (.leaf (0)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (0))) (.branch 50 (.leaf (3)) (.leaf (8))))))))
  code := certificateP9_6105
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.leaf (15)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 51 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 21 (.leaf (-6)) (.branch 38 (.leaf (-7)) (.leaf (-8))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 28 (.leaf (-19)) (.branch 34 (.leaf (-20)) (.leaf (-22))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-9)) (.leaf (-11)))),
  (.branch 13 (.leaf (0)) (.leaf (-25))),
  (.branch 7 (.leaf (0)) (.leaf (-37))),
  (.branch 20 (.leaf (0)) (.branch 45 (.leaf (-11)) (.leaf (-12)))),
  (.branch 26 (.leaf (0)) (.leaf (-25))),
  (.leaf (0))]
  high := ![(.branch 39 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4)))),
  (.branch 48 (.branch 35 (.leaf (-22)) (.leaf (-21))) (.branch 49 (.leaf (-16)) (.branch 50 (.leaf (-11)) (.leaf (-6))))),
  (.branch 31 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-6)))),
  (.branch 44 (.branch 41 (.branch 14 (.leaf (-25)) (.branch 40 (.leaf (-24)) (.leaf (-22)))) (.branch 42 (.leaf (-20)) (.branch 43 (.leaf (-18)) (.leaf (-16))))) (.branch 47 (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 41 (.branch 36 (.branch 34 (.branch 8 (.leaf (-37)) (.leaf (-36))) (.branch 35 (.leaf (-34)) (.leaf (-32)))) (.branch 38 (.branch 37 (.leaf (-30)) (.leaf (-28))) (.branch 39 (.leaf (-26)) (.branch 40 (.leaf (-24)) (.leaf (-22)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-20)) (.leaf (-18))) (.branch 44 (.leaf (-16)) (.branch 45 (.leaf (-14)) (.leaf (-12))))) (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 38 (.branch 32 (.branch 29 (.branch 27 (.leaf (-25)) (.branch 28 (.leaf (-24)) (.leaf (-23)))) (.branch 30 (.leaf (-22)) (.branch 31 (.leaf (-21)) (.leaf (-20))))) (.branch 35 (.branch 33 (.leaf (-19)) (.branch 34 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.leaf (-16)) (.branch 37 (.leaf (-15)) (.leaf (-14)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))) (.branch 42 (.leaf (-10)) (.branch 43 (.leaf (-9)) (.leaf (-8))))) (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_312_6106 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (3)) (.leaf (0))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (2)) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (1)) (.leaf (2))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (7)) (.leaf (1)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (0)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (4)) (.branch 40 (.leaf (1)) (.leaf (3)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (2)) (.leaf (1))))) (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (5)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (2)) (.leaf (0))) (.branch 50 (.leaf (8)) (.leaf (1))))))))
  code := certificateP9_6106
  counts := ![(.branch 25 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.leaf (15)))))),
  (.branch 27 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.leaf (15)))))),
  (.branch 26 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 43 (.leaf (7)) (.branch 48 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-12)) (.leaf (-14)))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 36 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-8)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 16 (.leaf (0)) (.leaf (-35))),
  (.branch 33 (.leaf (0)) (.leaf (-18))),
  (.branch 50 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 46 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 50 (.leaf (-10)) (.leaf (-5)))),
  (.branch 48 (.branch 37 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-2)) (.leaf (0)))),
  (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-6)) (.leaf (-3)))),
  (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (-35)) (.leaf (-34))) (.branch 19 (.leaf (-33)) (.leaf (-32)))) (.branch 22 (.branch 21 (.leaf (-31)) (.leaf (-30))) (.branch 23 (.leaf (-29)) (.leaf (-28))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-27)) (.leaf (-26))) (.branch 27 (.leaf (-25)) (.leaf (-24)))) (.branch 30 (.branch 29 (.leaf (-23)) (.leaf (-22))) (.branch 31 (.leaf (-21)) (.branch 32 (.leaf (-20)) (.leaf (-19))))))) (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-18)) (.leaf (-17))) (.branch 36 (.leaf (-16)) (.leaf (-15)))) (.branch 39 (.branch 38 (.leaf (-14)) (.leaf (-13))) (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-18)) (.leaf (-17))) (.branch 36 (.leaf (-16)) (.leaf (-15)))) (.branch 39 (.branch 38 (.leaf (-14)) (.leaf (-13))) (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_312_6107 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (7)) (.branch 11 (.leaf (4)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (5)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (8)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (1))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (7)) (.leaf (2)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (5))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (3)) (.leaf (8)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (4)) (.leaf (0)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (6)) (.branch 40 (.leaf (0)) (.leaf (2)))) (.branch 42 (.leaf (1)) (.branch 43 (.leaf (0)) (.leaf (7))))) (.branch 47 (.branch 45 (.leaf (3)) (.branch 46 (.leaf (0)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (5)) (.leaf (0))) (.branch 50 (.leaf (4)) (.leaf (8))))))))
  code := certificateP9_6107
  counts := ![(.branch 23 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 38 (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 43 (.branch 40 (.leaf (14)) (.leaf (15))) (.branch 46 (.leaf (16)) (.branch 49 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 28 (.leaf (-39)) (.leaf (-41)))),
  (.branch 7 (.leaf (0)) (.branch 45 (.leaf (-23)) (.leaf (-24)))),
  (.branch 11 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 44 (.branch 41 (.leaf (-15)) (.leaf (-14))) (.branch 47 (.leaf (-13)) (.branch 50 (.leaf (-12)) (.leaf (-6))))),
  (.branch 49 (.branch 48 (.leaf (-12)) (.leaf (-9))) (.branch 50 (.leaf (-6)) (.leaf (-3)))),
  (.branch 45 (.branch 42 (.branch 29 (.leaf (-41)) (.leaf (-40))) (.branch 43 (.leaf (-36)) (.branch 44 (.leaf (-32)) (.leaf (-28))))) (.branch 48 (.branch 46 (.leaf (-24)) (.branch 47 (.leaf (-20)) (.leaf (-16)))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 48 (.branch 46 (.leaf (-24)) (.branch 47 (.leaf (-20)) (.leaf (-16)))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4))))),
  (.branch 25 (.branch 12 (.leaf (-7)) (.leaf (-6))) (.branch 38 (.leaf (-5)) (.leaf (-4)))),
  (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessP9_312_6108 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (3)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1)))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (5)) (.leaf (2))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (0)) (.leaf (2))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (7)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (5)))) (.branch 42 (.leaf (2)) (.branch 43 (.leaf (0)) (.leaf (1))))) (.branch 47 (.branch 45 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (2)) (.leaf (1))) (.branch 50 (.leaf (8)) (.leaf (3))))))))
  code := certificateP9_6108
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 48 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 45 (.leaf (7)) (.branch 51 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 13 (.leaf (-15)) (.leaf (-16))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-10)))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 38 (.leaf (-3)) (.leaf (-4)))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 16 (.leaf (0)) (.leaf (-35))),
  (.branch 33 (.leaf (0)) (.leaf (-18))),
  (.branch 50 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 49 (.branch 48 (.leaf (-16)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4)))),
  (.branch 45 (.leaf (-11)) (.branch 50 (.leaf (-8)) (.leaf (-4)))),
  (.branch 49 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-6)) (.leaf (-3)))),
  (.branch 46 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.branch 48 (.leaf (-1)) (.leaf (0))))),
  (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (-35)) (.leaf (-34))) (.branch 19 (.leaf (-33)) (.leaf (-32)))) (.branch 22 (.branch 21 (.leaf (-31)) (.leaf (-30))) (.branch 23 (.leaf (-29)) (.leaf (-28))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-27)) (.leaf (-26))) (.branch 27 (.leaf (-25)) (.leaf (-24)))) (.branch 30 (.branch 29 (.leaf (-23)) (.leaf (-22))) (.branch 31 (.leaf (-21)) (.branch 32 (.leaf (-20)) (.leaf (-19))))))) (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-18)) (.leaf (-17))) (.branch 36 (.leaf (-16)) (.leaf (-15)))) (.branch 39 (.branch 38 (.leaf (-14)) (.leaf (-13))) (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-18)) (.leaf (-17))) (.branch 36 (.leaf (-16)) (.leaf (-15)))) (.branch 39 (.branch 38 (.leaf (-14)) (.leaf (-13))) (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_312_6109 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (6)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (4)))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (2)) (.leaf (1))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (3)) (.branch 27 (.leaf (0)) (.leaf (7)))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (1)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (2)) (.branch 33 (.leaf (5)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (4)) (.leaf (2)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (5)) (.leaf (3)))) (.branch 42 (.leaf (1)) (.branch 43 (.leaf (4)) (.leaf (0))))) (.branch 47 (.branch 45 (.leaf (8)) (.branch 46 (.leaf (2)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (3))) (.branch 50 (.leaf (5)) (.leaf (4))))))))
  code := certificateP9_6109
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.leaf (7))))),
  (.branch 26 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 29 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 38 (.leaf (-12)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 26 (.leaf (-7)) (.leaf (-8)))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 43 (.leaf (-3)) (.leaf (-4)))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (-3))) (.branch 40 (.leaf (-4)) (.leaf (-5)))),
  (.branch 11 (.leaf (0)) (.leaf (-40))),
  (.branch 28 (.leaf (0)) (.leaf (-23))),
  (.branch 45 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 49 (.branch 40 (.leaf (-14)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4)))),
  (.branch 49 (.branch 48 (.leaf (-12)) (.leaf (-9))) (.branch 50 (.leaf (-6)) (.leaf (-3)))),
  (.branch 48 (.branch 39 (.leaf (-14)) (.branch 47 (.leaf (-13)) (.leaf (-11)))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-7)) (.leaf (-5))))),
  (.branch 42 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.branch 44 (.leaf (-4)) (.branch 45 (.leaf (-2)) (.leaf (0)))),
  (.branch 41 (.leaf (-5)) (.leaf (-4))),
  (.branch 31 (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-40)) (.leaf (-39))) (.branch 14 (.leaf (-38)) (.branch 15 (.leaf (-37)) (.leaf (-36))))) (.branch 18 (.branch 17 (.leaf (-35)) (.leaf (-34))) (.branch 19 (.leaf (-33)) (.branch 20 (.leaf (-32)) (.leaf (-31)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-30)) (.leaf (-29))) (.branch 24 (.leaf (-28)) (.branch 25 (.leaf (-27)) (.leaf (-26))))) (.branch 28 (.branch 27 (.leaf (-25)) (.leaf (-24))) (.branch 29 (.leaf (-23)) (.branch 30 (.leaf (-22)) (.leaf (-21))))))) (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-20)) (.leaf (-19))) (.branch 34 (.leaf (-18)) (.branch 35 (.leaf (-17)) (.leaf (-16))))) (.branch 38 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 39 (.branch 33 (.branch 30 (.branch 29 (.leaf (-23)) (.leaf (-22))) (.branch 31 (.leaf (-21)) (.branch 32 (.leaf (-20)) (.leaf (-19))))) (.branch 36 (.branch 34 (.leaf (-18)) (.branch 35 (.leaf (-17)) (.leaf (-16)))) (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_312_6110 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (6)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (8)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (7))) (.branch 24 (.leaf (1)) (.leaf (5))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (6)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (1)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (8)) (.branch 33 (.leaf (2)) (.leaf (4)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (5)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (7)) (.leaf (1)))) (.branch 42 (.leaf (3)) (.branch 43 (.leaf (0)) (.leaf (2))))) (.branch 47 (.branch 45 (.leaf (6)) (.branch 46 (.leaf (4)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (8))) (.branch 50 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6110
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 41 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 37 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-35)) (.leaf (-37)))),
  (.branch 8 (.leaf (0)) (.branch 46 (.leaf (-19)) (.leaf (-20)))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 49 (.branch 44 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4)))),
  (.branch 48 (.branch 42 (.leaf (-13)) (.leaf (-12))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-6)) (.leaf (-3))))),
  (.branch 38 (.leaf (-5)) (.leaf (-4))),
  (.branch 46 (.branch 43 (.branch 30 (.leaf (-37)) (.leaf (-36))) (.branch 44 (.leaf (-32)) (.branch 45 (.leaf (-28)) (.leaf (-24))))) (.branch 48 (.branch 47 (.leaf (-20)) (.leaf (-16))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 48 (.branch 47 (.leaf (-20)) (.leaf (-16))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4))))),
  (.branch 26 (.branch 13 (.leaf (-3)) (.leaf (-2))) (.branch 39 (.leaf (-1)) (.leaf (0)))),
  (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_312_6111 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (7)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (6)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (3)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (8)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.leaf (5))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (6)))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (1)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (3)) (.branch 33 (.leaf (2)) (.leaf (7)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (5)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (3)) (.leaf (1)))) (.branch 42 (.leaf (4)) (.branch 43 (.leaf (0)) (.leaf (2))))) (.branch 47 (.branch 45 (.leaf (6)) (.branch 46 (.leaf (8)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (3))) (.branch 50 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6111
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 41 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 37 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-35)) (.leaf (-37)))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-35))),
  (.branch 21 (.leaf (0)) (.branch 46 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 49 (.branch 44 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4)))),
  (.branch 48 (.branch 42 (.leaf (-13)) (.leaf (-12))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-6)) (.leaf (-3))))),
  (.branch 38 (.leaf (-5)) (.leaf (-4))),
  (.branch 41 (.leaf (-5)) (.branch 50 (.leaf (-4)) (.leaf (-2)))),
  (.branch 46 (.branch 43 (.branch 30 (.leaf (-37)) (.leaf (-36))) (.branch 44 (.leaf (-32)) (.branch 45 (.leaf (-28)) (.leaf (-24))))) (.branch 48 (.branch 47 (.leaf (-20)) (.leaf (-16))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 26 (.branch 13 (.leaf (-3)) (.leaf (-2))) (.branch 39 (.leaf (-1)) (.leaf (0)))),
  (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 37 (.branch 35 (.branch 9 (.leaf (-35)) (.leaf (-34))) (.branch 36 (.leaf (-32)) (.leaf (-30)))) (.branch 39 (.branch 38 (.leaf (-28)) (.leaf (-26))) (.branch 40 (.leaf (-24)) (.branch 41 (.leaf (-22)) (.leaf (-20)))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-16))) (.branch 45 (.leaf (-14)) (.leaf (-12)))) (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))))]
def witnessP9_312_6112 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (6)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (3)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.leaf (4))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (7)))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (1)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (3)) (.branch 33 (.leaf (2)) (.leaf (4)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (5)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (3)) (.leaf (1)))) (.branch 42 (.leaf (4)) (.branch 43 (.leaf (0)) (.leaf (2))))) (.branch 47 (.branch 45 (.leaf (8)) (.branch 46 (.leaf (5)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (3))) (.branch 50 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_6112
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 41 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 37 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 11 (.leaf (0)) (.leaf (-40))),
  (.branch 28 (.leaf (0)) (.leaf (-23))),
  (.branch 45 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 49 (.branch 44 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4)))),
  (.branch 48 (.branch 42 (.leaf (-13)) (.leaf (-12))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-6)) (.leaf (-3))))),
  (.branch 38 (.leaf (-5)) (.leaf (-4))),
  (.branch 41 (.leaf (-5)) (.branch 50 (.leaf (-4)) (.leaf (-2)))),
  (.branch 43 (.leaf (-1)) (.leaf (0))),
  (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 31 (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-40)) (.leaf (-39))) (.branch 14 (.leaf (-38)) (.branch 15 (.leaf (-37)) (.leaf (-36))))) (.branch 18 (.branch 17 (.leaf (-35)) (.leaf (-34))) (.branch 19 (.leaf (-33)) (.branch 20 (.leaf (-32)) (.leaf (-31)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-30)) (.leaf (-29))) (.branch 24 (.leaf (-28)) (.branch 25 (.leaf (-27)) (.leaf (-26))))) (.branch 28 (.branch 27 (.leaf (-25)) (.leaf (-24))) (.branch 29 (.leaf (-23)) (.branch 30 (.leaf (-22)) (.leaf (-21))))))) (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-20)) (.leaf (-19))) (.branch 34 (.leaf (-18)) (.branch 35 (.leaf (-17)) (.leaf (-16))))) (.branch 38 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 39 (.branch 33 (.branch 30 (.branch 29 (.leaf (-23)) (.leaf (-22))) (.branch 31 (.leaf (-21)) (.branch 32 (.leaf (-20)) (.leaf (-19))))) (.branch 36 (.branch 34 (.leaf (-18)) (.branch 35 (.leaf (-17)) (.leaf (-16)))) (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_312_6113 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (6)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (8)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (7)) (.leaf (4))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 29 (.leaf (6)) (.branch 30 (.leaf (1)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (8)) (.branch 33 (.leaf (2)) (.leaf (4)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (3))) (.branch 37 (.leaf (1)) (.leaf (5)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (2)) (.leaf (7)))) (.branch 42 (.leaf (4)) (.branch 43 (.leaf (3)) (.leaf (0))))) (.branch 47 (.branch 45 (.leaf (1)) (.branch 46 (.leaf (6)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (8))) (.branch 50 (.leaf (3)) (.leaf (4))))))))
  code := certificateP9_6113
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.leaf (7))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.leaf (7))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-13)) (.leaf (-14)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))) (.branch 30 (.branch 23 (.leaf (-13)) (.leaf (-14))) (.branch 37 (.leaf (-15)) (.leaf (-16))))),
  (.branch 40 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 47 (.leaf (-10)) (.leaf (-11)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-3))) (.branch 20 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 49 (.branch 40 (.leaf (-14)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4)))),
  (.branch 47 (.branch 38 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-13)))) (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-9))) (.branch 50 (.leaf (-7)) (.leaf (-5))))),
  (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-9))) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.leaf (-5)),
  (.branch 43 (.leaf (-1)) (.leaf (0))),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))) (.branch 42 (.leaf (-10)) (.branch 43 (.leaf (-9)) (.leaf (-8))))) (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_312_6114 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (5)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (8)) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (3)) (.leaf (0))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (6)) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (5)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (7)) (.branch 33 (.leaf (3)) (.leaf (1)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (4))) (.branch 37 (.leaf (2)) (.leaf (6)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (3)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (5)) (.leaf (8))))) (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (2)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (4))) (.branch 50 (.leaf (3)) (.leaf (6))))))))
  code := certificateP9_6114
  counts := ![(.branch 25 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 31 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.leaf (15)))))),
  (.branch 21 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-6)))) (.branch 31 (.leaf (-7)) (.branch 48 (.leaf (-8)) (.leaf (-9))))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 27 (.leaf (-23)) (.leaf (-25)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.leaf (-35))),
  (.branch 38 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-39))),
  (.branch 19 (.leaf (0)) (.branch 44 (.leaf (-13)) (.leaf (-14))))]
  high := ![(.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.branch 48 (.branch 28 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-21)))) (.branch 49 (.leaf (-16)) (.branch 50 (.leaf (-11)) (.leaf (-6))))),
  (.branch 48 (.branch 38 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 42 (.leaf (-3)) (.leaf (-2))),
  (.branch 24 (.branch 11 (.leaf (-11)) (.leaf (-10))) (.branch 37 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-4))))),
  (.branch 45 (.branch 18 (.branch 5 (.leaf (-35)) (.leaf (-34))) (.branch 31 (.leaf (-33)) (.branch 44 (.leaf (-32)) (.leaf (-28))))) (.branch 48 (.branch 46 (.leaf (-24)) (.branch 47 (.leaf (-20)) (.leaf (-16)))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 39 (.leaf (-1)) (.leaf (0))),
  (.branch 41 (.branch 36 (.branch 33 (.branch 7 (.leaf (-39)) (.leaf (-38))) (.branch 34 (.leaf (-36)) (.branch 35 (.leaf (-34)) (.leaf (-32))))) (.branch 38 (.branch 37 (.leaf (-30)) (.leaf (-28))) (.branch 39 (.leaf (-26)) (.branch 40 (.leaf (-24)) (.leaf (-22)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-20)) (.leaf (-18))) (.branch 44 (.leaf (-16)) (.branch 45 (.leaf (-14)) (.leaf (-12))))) (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 47 (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2)))))]
def witnessP9_312_6115 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (1)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (5)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (8)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (3)) (.leaf (0))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (4)) (.branch 27 (.leaf (2)) (.leaf (1)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (6)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (5)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (7)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (3)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (4)) (.leaf (2))))) (.branch 47 (.branch 45 (.leaf (1)) (.branch 46 (.leaf (0)) (.leaf (8)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (0))) (.branch 50 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6115
  counts := ![(.branch 25 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.leaf (15)))))),
  (.branch 23 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-12))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))) (.branch 31 (.leaf (-10)) (.branch 48 (.leaf (-11)) (.leaf (-12))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 37 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-43))),
  (.branch 13 (.leaf (0)) (.branch 38 (.leaf (-25)) (.leaf (-26)))),
  (.branch 21 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 43 (.branch 36 (.leaf (-12)) (.leaf (-11))) (.branch 50 (.leaf (-10)) (.leaf (-5)))),
  (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-9)) (.leaf (-6)))),
  (.branch 38 (.leaf (-5)) (.leaf (-4))),
  (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-8)) (.leaf (-7))) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 40 (.branch 34 (.branch 31 (.branch 5 (.leaf (-43)) (.leaf (-42))) (.branch 32 (.leaf (-40)) (.branch 33 (.leaf (-38)) (.leaf (-36))))) (.branch 37 (.branch 35 (.leaf (-34)) (.branch 36 (.leaf (-32)) (.leaf (-30)))) (.branch 38 (.leaf (-28)) (.branch 39 (.leaf (-26)) (.leaf (-24)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-22)) (.leaf (-20))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-16)) (.leaf (-14))))) (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-26)) (.branch 40 (.leaf (-24)) (.leaf (-22)))) (.branch 42 (.leaf (-20)) (.branch 43 (.leaf (-18)) (.leaf (-16))))) (.branch 47 (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 48 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))))]
def witnessP9_312 : Fin 58 → CycleWitness 9 := ![witnessP9_312_6058, witnessP9_312_6059, witnessP9_312_6060, witnessP9_312_6061, witnessP9_312_6062, witnessP9_312_6063, witnessP9_312_6064, witnessP9_312_6065, witnessP9_312_6066, witnessP9_312_6067, witnessP9_312_6068, witnessP9_312_6069, witnessP9_312_6070, witnessP9_312_6071, witnessP9_312_6072, witnessP9_312_6073, witnessP9_312_6074, witnessP9_312_6075, witnessP9_312_6076, witnessP9_312_6077, witnessP9_312_6078, witnessP9_312_6079, witnessP9_312_6080, witnessP9_312_6081, witnessP9_312_6082, witnessP9_312_6083, witnessP9_312_6084, witnessP9_312_6085, witnessP9_312_6086, witnessP9_312_6087, witnessP9_312_6088, witnessP9_312_6089, witnessP9_312_6090, witnessP9_312_6091, witnessP9_312_6092, witnessP9_312_6093, witnessP9_312_6094, witnessP9_312_6095, witnessP9_312_6096, witnessP9_312_6097, witnessP9_312_6098, witnessP9_312_6099, witnessP9_312_6100, witnessP9_312_6101, witnessP9_312_6102, witnessP9_312_6103, witnessP9_312_6104, witnessP9_312_6105, witnessP9_312_6106, witnessP9_312_6107, witnessP9_312_6108, witnessP9_312_6109, witnessP9_312_6110, witnessP9_312_6111, witnessP9_312_6112, witnessP9_312_6113, witnessP9_312_6114, witnessP9_312_6115]
end RealPinwheel.FiveSixths


