-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_188
-- name    : RealPinwheel_FiveSixths_WitnessD8_188
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:34:34.640206+00:00
-- url     : https://prove2.me/theorems/42863a36-f8c7-433e-8f37-5f134485ef8b
-- title:
--   Exact witness block D8_188
-- statement:
--   These exact witnesses represent words 1973 through 1992 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1973–1992; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_188_1972 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (1)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (1)) (.leaf (5)))) (.branch 16 (.leaf (7)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (2)) (.leaf (4))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (6)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (5)) (.branch 32 (.leaf (2)) (.leaf (0)))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (0)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (1)) (.leaf (4)))) (.branch 40 (.leaf (7)) (.branch 41 (.leaf (0)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (1)))) (.branch 46 (.leaf (3)) (.branch 47 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_1972
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 25 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 45 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 42 (.leaf (8)) (.branch 47 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))) (.branch 38 (.branch 21 (.leaf (-10)) (.leaf (-15))) (.branch 45 (.leaf (-16)) (.leaf (-21))))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.branch 16 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))),
  (.branch 33 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 38 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 38 (.branch 33 (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_188_1973 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (1)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (7)) (.leaf (2)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (6)) (.leaf (5))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (7)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (4)) (.branch 32 (.leaf (3)) (.leaf (0)))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (1)) (.leaf (0)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (2)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (4))))) (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (0)) (.leaf (1)))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (7)) (.leaf (5))))))))
  code := certificateD8_1973
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 25 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 26 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-14)) (.leaf (-18)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 38 (.leaf (-12)) (.leaf (-13)))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (-3)) (.leaf (-5))))]
  high := ![(.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 41 (.branch 31 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-10)) (.leaf (-5))))),
  (.branch 40 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 43 (.branch 40 (.branch 39 (.leaf (-13)) (.leaf (-12))) (.branch 41 (.leaf (-11)) (.branch 42 (.leaf (-10)) (.leaf (-9))))) (.branch 45 (.branch 44 (.leaf (-8)) (.leaf (-7))) (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 30 (.leaf (-5)) (.leaf (-4)))]
def witnessD8_188_1974 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (7)) (.leaf (3)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (6)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (5))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (7)) (.leaf (4))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (1)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (5)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (6)) (.leaf (3)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (4))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (7)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (5))))))))
  code := certificateD8_1974
  counts := ![(.branch 22 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 28 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 31 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 43 (.leaf (14)) (.branch 46 (.leaf (15)) (.leaf (16))))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 42 (.branch 39 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_188_1975 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (3)) (.leaf (7)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (4)) (.leaf (6))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (5)) (.branch 32 (.leaf (2)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (3)) (.leaf (7)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (5)) (.leaf (6))))))))
  code := certificateD8_1975
  counts := ![(.branch 21 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 45 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 31 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 41 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_188_1976 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (5)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (4)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (6)))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (2))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (4)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (3)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (4)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (7)) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_1976
  counts := ![(.branch 21 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 45 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 40 (.leaf (7)) (.branch 46 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-37))),
  (.branch 27 (.leaf (0)) (.leaf (-21))),
  (.branch 43 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 43 (.leaf (-2)) (.leaf (-1))),
  (.branch 41 (.leaf (-8)) (.branch 47 (.leaf (-6)) (.leaf (-3)))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 40 (.leaf (-1)) (.leaf (0))),
  (.branch 29 (.branch 20 (.branch 15 (.branch 13 (.branch 12 (.leaf (-37)) (.leaf (-36))) (.branch 14 (.leaf (-35)) (.leaf (-34)))) (.branch 17 (.branch 16 (.leaf (-33)) (.leaf (-32))) (.branch 18 (.leaf (-31)) (.branch 19 (.leaf (-30)) (.leaf (-29)))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-28)) (.leaf (-27))) (.branch 23 (.leaf (-26)) (.leaf (-25)))) (.branch 26 (.branch 25 (.leaf (-24)) (.leaf (-23))) (.branch 27 (.leaf (-22)) (.branch 28 (.leaf (-21)) (.leaf (-20))))))) (.branch 38 (.branch 33 (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 37 (.branch 32 (.branch 29 (.branch 28 (.leaf (-21)) (.leaf (-20))) (.branch 30 (.leaf (-19)) (.branch 31 (.leaf (-18)) (.leaf (-17))))) (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_188_1977 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (6)) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (4))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (5)) (.branch 32 (.leaf (4)) (.leaf (2)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (1)))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (0)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (7)) (.branch 44 (.leaf (3)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (4))))))))
  code := certificateD8_1977
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 26 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 39 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 27 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 42 (.leaf (8)) (.branch 47 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 15 (.leaf (-4)) (.branch 39 (.leaf (-5)) (.leaf (-6))))),
  (.branch 3 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-17))),
  (.branch 19 (.leaf (0)) (.leaf (-29))),
  (.branch 43 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 42 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 40 (.leaf (-6)) (.leaf (-5))) (.branch 47 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 37 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.leaf (-10))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 26 (.branch 22 (.branch 20 (.leaf (-29)) (.branch 21 (.leaf (-28)) (.leaf (-27)))) (.branch 24 (.branch 23 (.leaf (-26)) (.leaf (-25))) (.branch 25 (.leaf (-24)) (.leaf (-23))))) (.branch 29 (.branch 27 (.leaf (-22)) (.branch 28 (.leaf (-21)) (.leaf (-20)))) (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))))) (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_188_1978 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (2)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (3)) (.leaf (0)))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (0)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (5)) (.branch 23 (.leaf (3)) (.leaf (7))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (4)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (3)))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (2)) (.leaf (0)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (4)) (.leaf (0)))) (.branch 40 (.leaf (7)) (.branch 41 (.leaf (0)) (.leaf (3))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (5)) (.branch 47 (.leaf (4)) (.leaf (6))))))))
  code := certificateD8_1978
  counts := ![(.branch 21 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 29 (.branch 25 (.leaf (7)) (.leaf (8))) (.branch 32 (.leaf (9)) (.leaf (10)))) (.branch 41 (.branch 39 (.leaf (11)) (.leaf (12))) (.branch 45 (.leaf (13)) (.leaf (14)))))),
  (.branch 20 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-9)))) (.branch 17 (.leaf (-10)) (.branch 41 (.leaf (-15)) (.leaf (-20))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 30 (.leaf (-14)) (.leaf (-18)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 23 (.branch 4 (.leaf (0)) (.leaf (-28))) (.branch 42 (.leaf (-29)) (.leaf (-30)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-3)) (.leaf (-6)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 31 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 46 (.branch 42 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-16)) (.leaf (-13)))),
  (.branch 45 (.branch 31 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-14)) (.branch 47 (.leaf (-12)) (.leaf (-10))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 43 (.leaf (-30)) (.branch 44 (.leaf (-25)) (.leaf (-20)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-10)) (.leaf (-5))))),
  (.branch 19 (.leaf (-6)) (.leaf (-5))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 43 (.branch 41 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_188_1979 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (2)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2)))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (7)) (.leaf (4)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (1))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (4)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (1)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (6)) (.branch 32 (.leaf (5)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (3)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (4))))) (.branch 45 (.branch 43 (.leaf (7)) (.branch 44 (.leaf (3)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_1979
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 25 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 29 (.leaf (5)) (.leaf (6))) (.branch 40 (.leaf (7)) (.branch 45 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 27 (.leaf (-6)) (.branch 39 (.leaf (-8)) (.leaf (-10))))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 26 (.leaf (-10)) (.branch 42 (.leaf (-14)) (.leaf (-18))))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 31 (.leaf (-16)) (.leaf (-17)))),
  (.branch 20 (.leaf (0)) (.branch 43 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 42 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-6)) (.leaf (-3))))),
  (.branch 40 (.leaf (-10)) (.leaf (-9))),
  (.branch 45 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13))))),
  (.leaf (0)),
  (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 37 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.leaf (-10))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_188_1980 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (3)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (4)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (5)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (3)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (7)) (.leaf (2)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (1)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (5)) (.branch 44 (.leaf (0)) (.leaf (4)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (3)) (.leaf (2))))))))
  code := certificateD8_1980
  counts := ![(.branch 20 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 25 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 39 (.leaf (8)) (.branch 44 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 26 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 41 (.leaf (8)) (.branch 46 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 27 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 42 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-19)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 3 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 19 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-40))),
  (.branch 32 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 45 (.branch 35 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-10)) (.leaf (-5))))),
  (.branch 37 (.branch 27 (.leaf (-14)) (.branch 32 (.leaf (-13)) (.leaf (-12)))) (.branch 42 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-5))))),
  (.branch 44 (.branch 43 (.leaf (-3)) (.leaf (-2))) (.branch 45 (.leaf (-1)) (.leaf (0)))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-40)) (.leaf (-39))) (.branch 11 (.leaf (-38)) (.branch 12 (.leaf (-37)) (.leaf (-36))))) (.branch 15 (.branch 14 (.leaf (-35)) (.leaf (-34))) (.branch 16 (.leaf (-33)) (.branch 17 (.leaf (-32)) (.leaf (-31)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-30)) (.leaf (-29))) (.branch 21 (.leaf (-28)) (.branch 22 (.leaf (-27)) (.leaf (-26))))) (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.branch 27 (.leaf (-22)) (.leaf (-21))))))) (.branch 38 (.branch 33 (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_188_1981 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (3)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (7)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (3)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (5)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (6)) (.leaf (2)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (1)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (7)) (.branch 44 (.leaf (0)) (.leaf (5)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (3)) (.leaf (2))))))))
  code := certificateD8_1981
  counts := ![(.branch 20 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 25 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 39 (.leaf (8)) (.branch 44 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 26 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 41 (.leaf (8)) (.branch 46 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 27 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 42 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-19)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 3 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 19 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 45 (.branch 35 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-10)) (.leaf (-5))))),
  (.branch 37 (.branch 27 (.leaf (-14)) (.branch 32 (.leaf (-13)) (.leaf (-12)))) (.branch 42 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-5))))),
  (.branch 44 (.branch 43 (.leaf (-3)) (.leaf (-2))) (.branch 45 (.leaf (-1)) (.leaf (0)))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 42 (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_188_1982 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (4)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (5)))) (.branch 16 (.leaf (7)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (6))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (5)))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (4)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (3)) (.branch 32 (.leaf (7)) (.leaf (1)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (3)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (4)) (.leaf (1)))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (5)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (1)) (.leaf (3)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (7))))))))
  code := certificateD8_1982
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 25 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 28 (.leaf (5)) (.leaf (6))) (.branch 39 (.leaf (7)) (.branch 44 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 12 (.leaf (-11)) (.branch 17 (.leaf (-12)) (.leaf (-13))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-26))) (.branch 26 (.leaf (-27)) (.leaf (-34)))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 36 (.leaf (-6)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.branch 47 (.leaf (-2)) (.leaf (-4)))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (-8))) (.branch 27 (.leaf (-11)) (.leaf (-12)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 38 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 34 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-6)) (.leaf (-3))))),
  (.branch 45 (.branch 27 (.leaf (-34)) (.branch 44 (.leaf (-31)) (.leaf (-26)))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-16)) (.leaf (-11))))),
  (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7)))),
  (.leaf (-4)),
  (.branch 44 (.branch 42 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9)))) (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5))))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_188_1983 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (5)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (6)) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (5)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))) (.branch 28 (.leaf (4)) (.branch 29 (.leaf (0)) (.leaf (2))))) (.branch 33 (.branch 31 (.leaf (7)) (.branch 32 (.leaf (0)) (.leaf (1)))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (5)) (.leaf (0)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (3)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (6)) (.branch 44 (.leaf (2)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (5)) (.leaf (3))))))))
  code := certificateD8_1983
  counts := ![(.branch 22 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 29 (.branch 25 (.leaf (7)) (.leaf (8))) (.branch 32 (.leaf (9)) (.leaf (10)))) (.branch 42 (.branch 39 (.leaf (11)) (.leaf (12))) (.branch 46 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 30 (.leaf (-27)) (.leaf (-30)))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 19 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 43 (.leaf (-18)) (.branch 47 (.leaf (-14)) (.leaf (-7)))),
  (.branch 46 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 31 (.leaf (-30)) (.branch 38 (.leaf (-29)) (.leaf (-28)))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-14)) (.leaf (-7))))),
  (.branch 21 (.branch 7 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 35 (.branch 28 (.leaf (-3)) (.leaf (-2))) (.branch 42 (.leaf (-1)) (.leaf (0))))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 37 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.leaf (-10))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_188_1984 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (7)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (6)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (3)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (7)) (.leaf (5))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (6))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (5)) (.branch 29 (.leaf (7)) (.leaf (3))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (6)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (5)) (.branch 38 (.leaf (1)) (.leaf (3)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (7)) (.leaf (4))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (3)) (.branch 47 (.leaf (5)) (.leaf (6))))))))
  code := certificateD8_1984
  counts := ![(.branch 21 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 25 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 34 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-28)) (.leaf (-31)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (-3))) (.branch 37 (.leaf (-6)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 46 (.branch 35 (.leaf (-6)) (.leaf (-5))) (.branch 47 (.leaf (-4)) (.leaf (-3)))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.branch 14 (.leaf (-31)) (.branch 43 (.leaf (-30)) (.leaf (-25)))) (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-15))) (.branch 47 (.leaf (-10)) (.leaf (-5))))),
  (.branch 38 (.leaf (-7)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_188_1985 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (2)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (3)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (6)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (1)) (.leaf (4)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (5)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (4)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (0)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (3)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (7)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (1)) (.leaf (4)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (1))))))))
  code := certificateD8_1985
  counts := ![(.branch 22 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 29 (.branch 25 (.leaf (7)) (.leaf (8))) (.branch 32 (.leaf (9)) (.leaf (10)))) (.branch 42 (.branch 39 (.leaf (11)) (.leaf (12))) (.branch 46 (.leaf (13)) (.leaf (14)))))),
  (.branch 24 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 48 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-20))),
  (.branch 17 (.leaf (0)) (.leaf (-31))),
  (.branch 41 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 43 (.leaf (-18)) (.branch 47 (.leaf (-14)) (.leaf (-7)))),
  (.branch 45 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 46 (.leaf (-1)) (.leaf (0)))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 33 (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 24 (.branch 20 (.branch 18 (.leaf (-31)) (.branch 19 (.leaf (-30)) (.leaf (-29)))) (.branch 22 (.branch 21 (.leaf (-28)) (.leaf (-27))) (.branch 23 (.leaf (-26)) (.leaf (-25))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-24)) (.leaf (-23))) (.branch 27 (.leaf (-22)) (.leaf (-21)))) (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.leaf (-17)))))) (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_188_1986 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (2)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (7)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (6))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (5)) (.branch 29 (.leaf (0)) (.leaf (3))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (7)) (.leaf (0)))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (2)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (6)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (3))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (4)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_1986
  counts := ![(.branch 23 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 29 (.branch 25 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 26 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 41 (.leaf (8)) (.branch 46 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 25 (.leaf (-8)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (-9))) (.branch 38 (.leaf (-12)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.branch 39 (.leaf (-8)) (.leaf (-9)))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.leaf (-13)),
  (.branch 37 (.branch 27 (.leaf (-14)) (.branch 32 (.leaf (-13)) (.leaf (-12)))) (.branch 42 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-5))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 43 (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-1)) (.leaf (0)))]
def witnessD8_188_1987 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (7)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (5)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 22 (.leaf (6)) (.branch 23 (.leaf (2)) (.leaf (3))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (5)) (.branch 29 (.leaf (0)) (.leaf (7))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (4)) (.leaf (2)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (6)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (5)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (4)) (.branch 44 (.leaf (0)) (.leaf (1)))) (.branch 46 (.leaf (7)) (.branch 47 (.leaf (2)) (.leaf (3))))))))
  code := certificateD8_1987
  counts := ![(.branch 20 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 25 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 39 (.leaf (8)) (.branch 44 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 26 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 42 (.leaf (8)) (.branch 47 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-19)) (.leaf (-23)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-14)) (.leaf (-17)))),
  (.branch 3 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 40 (.branch 30 (.leaf (-23)) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-15))) (.branch 47 (.leaf (-10)) (.leaf (-5))))),
  (.branch 41 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-3)),
  (.leaf (0)),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.branch 42 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_188_1988 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (4)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (6))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (3)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))) (.branch 28 (.leaf (4)) (.branch 29 (.leaf (0)) (.leaf (7))))) (.branch 33 (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (5)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (3)) (.leaf (6))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (4)) (.leaf (2)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_1988
  counts := ![(.branch 23 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 29 (.branch 25 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 43 (.branch 39 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 22 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 26 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 46 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 25 (.leaf (-10)) (.branch 39 (.leaf (-13)) (.leaf (-15))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 40 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-27))),
  (.branch 27 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 35 (.leaf (-12)) (.leaf (-13)))),
  (.branch 18 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-18)))]
  high := ![(.branch 40 (.leaf (-15)) (.branch 44 (.leaf (-14)) (.leaf (-13)))),
  (.branch 41 (.leaf (-5)) (.branch 47 (.leaf (-4)) (.leaf (-3)))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (-27)) (.leaf (-26))) (.branch 18 (.leaf (-25)) (.leaf (-24)))) (.branch 39 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-14)) (.leaf (-7)))))),
  (.branch 35 (.branch 28 (.leaf (-3)) (.leaf (-2))) (.branch 42 (.leaf (-1)) (.leaf (0)))),
  (.branch 45 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 41 (.branch 38 (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))) (.branch 39 (.leaf (-10)) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 34 (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_188_1989 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (7)) (.branch 11 (.leaf (6)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (1)) (.leaf (4)))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (1)) (.leaf (4)))) (.branch 22 (.leaf (6)) (.branch 23 (.leaf (0)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (7)) (.branch 26 (.leaf (1)) (.leaf (3)))) (.branch 28 (.leaf (5)) (.branch 29 (.leaf (0)) (.leaf (4))))) (.branch 33 (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (6)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (3)) (.leaf (7))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (4)) (.branch 47 (.leaf (3)) (.leaf (6))))))))
  code := certificateD8_1989
  counts := ![(.branch 23 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 29 (.leaf (5)) (.leaf (6))) (.branch 39 (.leaf (7)) (.branch 45 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-22))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 36 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (-7))) (.branch 37 (.leaf (-12)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-3)) (.leaf (-6)))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (-6)) (.leaf (-7))))]
  high := ![(.branch 40 (.branch 2 (.leaf (-22)) (.leaf (-21))) (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-13)) (.leaf (-8))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 44 (.leaf (-6)) (.leaf (-5))) (.branch 46 (.leaf (-4)) (.branch 47 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 38 (.leaf (-14)) (.branch 47 (.leaf (-12)) (.leaf (-9)))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 23 (.leaf (-6)) (.leaf (-5))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-1)) (.leaf (0))))),
  (.branch 44 (.branch 26 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_188_1990 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (3)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (5)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (7)) (.branch 23 (.leaf (4)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (5)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 34 (.leaf (6)) (.branch 35 (.leaf (3)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (4)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (7)) (.branch 47 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_1990
  counts := ![(.branch 21 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 33 (.branch 28 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 30 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 42 (.leaf (14)) (.branch 45 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-14))),
  (.branch 22 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 41 (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_188_1991 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (5)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (3)))) (.branch 16 (.leaf (7)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (5)) (.leaf (6))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (4)) (.branch 32 (.leaf (7)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (5)) (.leaf (0)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (3)))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (4)) (.branch 44 (.leaf (0)) (.leaf (2)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (5)) (.leaf (7))))))))
  code := certificateD8_1991
  counts := ![(.branch 22 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))) (.branch 36 (.branch 28 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.branch 33 (.leaf (12)) (.leaf (13))))) (.branch 41 (.branch 38 (.leaf (14)) (.leaf (15))) (.branch 44 (.leaf (16)) (.branch 46 (.leaf (17)) (.leaf (18))))))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 47 (.leaf (-6)) (.leaf (-3))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_188 : Fin 20 → CycleWitness 8 := ![witnessD8_188_1972, witnessD8_188_1973, witnessD8_188_1974, witnessD8_188_1975, witnessD8_188_1976, witnessD8_188_1977, witnessD8_188_1978, witnessD8_188_1979, witnessD8_188_1980, witnessD8_188_1981, witnessD8_188_1982, witnessD8_188_1983, witnessD8_188_1984, witnessD8_188_1985, witnessD8_188_1986, witnessD8_188_1987, witnessD8_188_1988, witnessD8_188_1989, witnessD8_188_1990, witnessD8_188_1991]
end RealPinwheel.FiveSixths


