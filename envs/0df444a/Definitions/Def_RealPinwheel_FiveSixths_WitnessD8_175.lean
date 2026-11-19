-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_175
-- name    : RealPinwheel_FiveSixths_WitnessD8_175
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:26:20.830259+00:00
-- url     : https://prove2.me/theorems/9a56bcf4-7a2a-40f7-b6f5-88e026da19d2
-- title:
--   Exact witness block D8_175
-- statement:
--   These exact witnesses represent words 1723 through 1740 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1723–1740; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_175_1722 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (5)) (.leaf (7)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (6)) (.branch 22 (.leaf (3)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (5))) (.branch 26 (.leaf (1)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 31 (.leaf (7)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (4)) (.branch 35 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (5)) (.leaf (6)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (0)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (4))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (7)) (.branch 49 (.leaf (3)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (5))) (.branch 53 (.leaf (2)) (.leaf (4))))))))
  code := certificateD8_1722
  counts := ![(.branch 24 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 22 (.leaf (-5)) (.branch 49 (.leaf (-6)) (.leaf (-7))))),
  (.branch 7 (.leaf (0)) (.branch 34 (.leaf (-3)) (.leaf (-6)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-14)) (.leaf (-15)))),
  (.branch 13 (.leaf (0)) (.branch 48 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 52 (.branch 47 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 51 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3))))),
  (.branch 47 (.branch 35 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.branch 48 (.leaf (-3)) (.leaf (-2))) (.branch 50 (.leaf (-1)) (.leaf (0))))),
  (.branch 53 (.leaf (-4)) (.leaf (-2))),
  (.branch 46 (.branch 42 (.branch 22 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_175_1723 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (7)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (6))) (.branch 26 (.leaf (1)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (4)) (.leaf (0)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (5)) (.branch 35 (.leaf (7)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (6)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (3)) (.branch 42 (.leaf (0)) (.leaf (4)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (5))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (3)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (6))) (.branch 53 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_1723
  counts := ![(.branch 24 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))) (.branch 40 (.branch 30 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.branch 37 (.leaf (12)) (.leaf (13))))) (.branch 46 (.branch 42 (.leaf (14)) (.leaf (15))) (.branch 48 (.leaf (16)) (.branch 51 (.leaf (17)) (.leaf (18))))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 29 (.leaf (-22)) (.leaf (-23)))),
  (.branch 7 (.leaf (0)) (.branch 47 (.leaf (-13)) (.leaf (-14)))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 48 (.branch 45 (.branch 30 (.leaf (-23)) (.branch 44 (.leaf (-22)) (.leaf (-20)))) (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-16)) (.leaf (-14))))) (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 50 (.branch 48 (.leaf (-14)) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 12 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1))]
def witnessD8_175_1724 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (7)) (.leaf (6))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (6)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (1)) (.leaf (0))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (7)) (.branch 29 (.leaf (5)) (.leaf (0)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (6)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (5)) (.leaf (2)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (3)) (.leaf (6)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (0))) (.branch 46 (.leaf (7)) (.leaf (4))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (2)) (.leaf (5)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (3)) (.leaf (6))))))))
  code := certificateD8_1724
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.leaf (15)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 51 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 42 (.leaf (-6)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-39))),
  (.branch 7 (.leaf (0)) (.branch 39 (.leaf (-19)) (.leaf (-21)))),
  (.branch 21 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 49 (.branch 38 (.leaf (-13)) (.leaf (-12))) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.branch 52 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.leaf (-8)) (.leaf (-7))),
  (.branch 48 (.branch 15 (.branch 4 (.leaf (-39)) (.leaf (-38))) (.branch 26 (.leaf (-37)) (.branch 37 (.leaf (-36)) (.leaf (-35))))) (.branch 51 (.branch 49 (.leaf (-30)) (.branch 50 (.leaf (-25)) (.leaf (-20)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 51 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 33 (.branch 22 (.leaf (-3)) (.leaf (-2))) (.branch 44 (.leaf (-1)) (.leaf (0)))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_175_1725 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (6)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (4)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (5)))) (.branch 18 (.branch 17 (.leaf (7)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (4)) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (4)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (5)) (.branch 35 (.leaf (7)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (4)) (.leaf (3)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (5)))) (.branch 45 (.branch 44 (.leaf (6)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (3))))) (.branch 50 (.branch 48 (.leaf (4)) (.branch 49 (.leaf (1)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (5))) (.branch 53 (.leaf (7)) (.leaf (3))))))))
  code := certificateD8_1725
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-19)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.branch 43 (.leaf (-21)) (.branch 50 (.leaf (-20)) (.leaf (-16)))) (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-8)) (.leaf (-4)))),
  (.branch 41 (.branch 34 (.leaf (-3)) (.leaf (-2))) (.branch 48 (.leaf (-1)) (.leaf (0)))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_175_1726 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (6)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (4)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (7)) (.leaf (1))) (.branch 26 (.leaf (6)) (.leaf (0))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (3)) (.branch 29 (.leaf (1)) (.leaf (4)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (5)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (6)) (.leaf (2)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (7)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (4)) (.leaf (0))) (.branch 46 (.leaf (3)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (5)) (.branch 49 (.leaf (0)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (6)) (.leaf (3))))))))
  code := certificateD8_1726
  counts := ![(.branch 27 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 34 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.leaf (15)))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 19 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 37 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-21))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (-11)) (.leaf (-12)))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 38 (.leaf (-10)) (.branch 53 (.leaf (-9)) (.leaf (-6)))),
  (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 48 (.branch 45 (.branch 31 (.leaf (-21)) (.leaf (-20))) (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-16)) (.leaf (-14))))) (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 40 (.leaf (-3)) (.leaf (-2))),
  (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_175_1727 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (7)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (5))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (4))) (.branch 26 (.leaf (6)) (.leaf (1))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (5)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (7)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (3)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (5)) (.branch 42 (.leaf (0)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (6)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (4))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (3)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (5))) (.branch 53 (.leaf (7)) (.leaf (1))))))))
  code := certificateD8_1727
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 23 (.leaf (-7)) (.leaf (-8)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 29 (.leaf (-4)) (.branch 43 (.leaf (-6)) (.leaf (-7))))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (-11)) (.leaf (-12)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-9))) (.branch 39 (.leaf (-14)) (.leaf (-17)))),
  (.branch 3 (.leaf (0)) (.leaf (-39))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (-9)) (.leaf (-12)))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.branch 49 (.leaf (-7)) (.branch 50 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.leaf (-4)) (.branch 53 (.leaf (-3)) (.leaf (-2))))),
  (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-8)) (.leaf (-4)))),
  (.branch 51 (.branch 40 (.leaf (-17)) (.branch 50 (.leaf (-16)) (.leaf (-14)))) (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-10)) (.leaf (-8))))),
  (.branch 48 (.branch 15 (.branch 4 (.leaf (-39)) (.leaf (-38))) (.branch 26 (.leaf (-37)) (.branch 37 (.leaf (-36)) (.leaf (-35))))) (.branch 51 (.branch 49 (.leaf (-30)) (.branch 50 (.leaf (-25)) (.leaf (-20)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 42 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_175_1728 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (0)) (.leaf (5)))) (.branch 18 (.branch 17 (.leaf (7)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (4)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (7)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (4))) (.branch 39 (.leaf (1)) (.leaf (2)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (3)) (.branch 42 (.leaf (0)) (.leaf (5)))) (.branch 45 (.branch 44 (.leaf (6)) (.leaf (1))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (5))) (.branch 53 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_1728
  counts := ![(.branch 24 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 29 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 12 (.leaf (-19)) (.leaf (-21)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 48 (.leaf (-15)) (.leaf (-18)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 30 (.leaf (-9)) (.branch 38 (.leaf (-10)) (.leaf (-12))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-4)))) (.branch 43 (.leaf (-5)) (.branch 52 (.leaf (-7)) (.leaf (-8))))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 47 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 51 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 41 (.branch 34 (.leaf (-3)) (.leaf (-2))) (.branch 48 (.leaf (-1)) (.leaf (0)))),
  (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-16)) (.leaf (-14)))) (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-10)) (.leaf (-8))))),
  (.branch 51 (.branch 39 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))),
  (.branch 53 (.leaf (-8)) (.leaf (-7))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_175_1729 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (5)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (1)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (5)) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (6)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (4)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (5)) (.leaf (7)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (0)) (.leaf (6)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (3))) (.branch 46 (.leaf (4)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (2)) (.branch 49 (.leaf (1)) (.leaf (5)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (6)) (.leaf (3))))))))
  code := certificateD8_1729
  counts := ![(.branch 24 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 49 (.leaf (8)) (.leaf (9)))))),
  (.branch 30 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 34 (.leaf (-7)) (.branch 52 (.leaf (-10)) (.leaf (-13))))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 35 (.leaf (-39)) (.leaf (-41)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-19)) (.leaf (-23)))),
  (.branch 10 (.leaf (0)) (.branch 53 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 52 (.branch 38 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.leaf (-13)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 49 (.branch 47 (.branch 36 (.leaf (-41)) (.leaf (-40))) (.branch 48 (.leaf (-35)) (.leaf (-30)))) (.branch 51 (.branch 50 (.leaf (-25)) (.leaf (-20))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 40 (.branch 18 (.leaf (-23)) (.branch 29 (.leaf (-22)) (.leaf (-21)))) (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-5)),
  (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_175_1730 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (2)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (2))) (.branch 12 (.leaf (5)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (6)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (7)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (6)) (.branch 29 (.leaf (1)) (.leaf (5)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (4))))) (.branch 36 (.branch 34 (.leaf (3)) (.branch 35 (.leaf (6)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (5)) (.leaf (7)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (2))) (.branch 46 (.leaf (6)) (.leaf (3))))) (.branch 50 (.branch 48 (.leaf (5)) (.branch 49 (.leaf (1)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (4)) (.leaf (2))) (.branch 53 (.leaf (6)) (.leaf (3))))))))
  code := certificateD8_1730
  counts := ![(.branch 26 (.branch 8 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 10 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.branch 49 (.leaf (-19)) (.leaf (-20)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 31 (.leaf (-10)) (.leaf (-11)))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (-3))) (.branch 53 (.leaf (-5)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 51 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.branch 50 (.leaf (-20)) (.leaf (-16))) (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 39 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 14 (.leaf (-2)) (.branch 48 (.leaf (-1)) (.leaf (0)))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-7)),
  (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_175_1731 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (7)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (6)) (.branch 22 (.leaf (0)) (.leaf (5)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (7)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (6)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (3))) (.branch 46 (.leaf (0)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (7)) (.branch 49 (.leaf (0)) (.leaf (5)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (2)) (.leaf (4))))))))
  code := certificateD8_1731
  counts := ![(.branch 25 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))) (.branch 40 (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.branch 37 (.leaf (12)) (.leaf (13))))) (.branch 46 (.branch 43 (.leaf (14)) (.leaf (15))) (.branch 49 (.leaf (16)) (.branch 52 (.leaf (17)) (.leaf (18))))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 12 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1)),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-18)) (.leaf (-16))) (.branch 48 (.leaf (-14)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (0)),
  (.branch 51 (.branch 37 (.leaf (-9)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_175_1732 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (2))) (.branch 26 (.leaf (1)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (1)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (6)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (1)) (.leaf (3)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (4)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (3))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (4)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (3))) (.branch 53 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_1732
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 45 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 31 (.leaf (-7)) (.branch 49 (.leaf (-9)) (.leaf (-11))))),
  (.branch 18 (.leaf (0)) (.leaf (-36))),
  (.branch 36 (.leaf (0)) (.leaf (-18))),
  (.leaf (0))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 49 (.leaf (-3)) (.leaf (-2))),
  (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 46 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))),
  (.branch 36 (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (-36)) (.leaf (-35))) (.branch 21 (.leaf (-34)) (.leaf (-33)))) (.branch 24 (.branch 23 (.leaf (-32)) (.leaf (-31))) (.branch 25 (.leaf (-30)) (.branch 26 (.leaf (-29)) (.leaf (-28)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-27)) (.leaf (-26))) (.branch 30 (.leaf (-25)) (.leaf (-24)))) (.branch 33 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))))) (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-14)) (.leaf (-13))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-14)) (.leaf (-13))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_175_1733 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (6)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (4))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (2)) (.leaf (6)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (0))) (.branch 26 (.leaf (5)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (7)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (4)) (.branch 35 (.leaf (2)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (1)) (.leaf (4)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (6)) (.branch 42 (.leaf (2)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (5)) (.leaf (3))) (.branch 46 (.leaf (1)) (.leaf (4))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (2)) (.leaf (7)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (3))) (.branch 53 (.leaf (4)) (.leaf (5))))))))
  code := certificateD8_1733
  counts := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 43 (.leaf (7)) (.branch 48 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 46 (.leaf (7)) (.branch 51 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 22 (.branch 2 (.leaf (0)) (.leaf (-24))) (.branch 35 (.leaf (-26)) (.leaf (-29)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-14)) (.leaf (-17)))),
  (.branch 6 (.leaf (0)) (.branch 53 (.leaf (-4)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 50 (.branch 36 (.leaf (-29)) (.branch 43 (.leaf (-28)) (.leaf (-27)))) (.branch 52 (.branch 51 (.leaf (-22)) (.leaf (-17))) (.branch 53 (.leaf (-12)) (.leaf (-7))))),
  (.branch 32 (.branch 18 (.leaf (-17)) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 46 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 53 (.leaf (-12)) (.leaf (-7))))),
  (.leaf (-7)),
  (.branch 45 (.leaf (-1)) (.leaf (0))),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_175_1734 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (5)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (7)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (4)) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (6)) (.leaf (2))) (.branch 26 (.leaf (5)) (.leaf (1))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (7))))) (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (4)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (5)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (6)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (3)) (.leaf (1))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (4)) (.branch 49 (.leaf (1)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (7)) (.leaf (2))) (.branch 53 (.leaf (5)) (.leaf (1))))))))
  code := certificateD8_1734
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-21))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (-11)) (.leaf (-12)))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 50 (.leaf (-1)) (.leaf (0))),
  (.branch 48 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.branch 45 (.branch 31 (.leaf (-21)) (.leaf (-20))) (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-16)) (.leaf (-14))))) (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 40 (.leaf (-3)) (.leaf (-2))),
  (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_175_1735 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (7)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (6)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (1)) (.leaf (7)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (6))) (.branch 26 (.leaf (2)) (.leaf (1))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (3)) (.leaf (4)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (5)) (.branch 35 (.leaf (1)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (6)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (7)) (.branch 42 (.leaf (0)) (.leaf (4)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (1))) (.branch 46 (.leaf (0)) (.leaf (3))))) (.branch 50 (.branch 48 (.leaf (5)) (.branch 49 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (6))) (.branch 53 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_1735
  counts := ![(.branch 24 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 11 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-21)) (.leaf (-22)))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 52 (.branch 47 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 48 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.branch 50 (.leaf (-1)) (.leaf (0))))),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-22)) (.leaf (-20))) (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-16)) (.leaf (-14))))) (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 50 (.branch 35 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 53 (.leaf (-4)) (.leaf (-2))),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_175_1736 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (5)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (3))) (.branch 26 (.leaf (1)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (3)) (.leaf (1)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (6))))) (.branch 36 (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (1)) (.leaf (2)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (4)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (3))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (2)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (7)) (.leaf (3))) (.branch 53 (.leaf (1)) (.leaf (2))))))))
  code := certificateD8_1736
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1))),
  (.branch 51 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-39))),
  (.branch 33 (.leaf (0)) (.leaf (-21))),
  (.branch 51 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 49 (.leaf (-3)) (.leaf (-2))),
  (.branch 50 (.leaf (-1)) (.leaf (0))),
  (.branch 48 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 24 (.branch 19 (.branch 17 (.branch 16 (.leaf (-39)) (.leaf (-38))) (.branch 18 (.leaf (-37)) (.leaf (-36)))) (.branch 21 (.branch 20 (.leaf (-35)) (.leaf (-34))) (.branch 22 (.leaf (-33)) (.branch 23 (.leaf (-32)) (.leaf (-31)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-30)) (.leaf (-29))) (.branch 27 (.leaf (-28)) (.branch 28 (.leaf (-27)) (.leaf (-26))))) (.branch 31 (.branch 30 (.leaf (-25)) (.leaf (-24))) (.branch 32 (.leaf (-23)) (.branch 33 (.leaf (-22)) (.leaf (-21))))))) (.branch 44 (.branch 39 (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16))))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 38 (.branch 35 (.branch 34 (.leaf (-21)) (.leaf (-20))) (.branch 36 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17))))) (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))))) (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_175_1737 : CycleWitness 8 where
  length := 53
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (5)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (6)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (4)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (7)) (.leaf (0)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (3))) (.branch 25 (.leaf (6)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 30 (.leaf (4)) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (5)) (.branch 34 (.leaf (7)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (0))) (.branch 38 (.leaf (1)) (.leaf (4)))))) (.branch 46 (.branch 42 (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (3)))) (.branch 44 (.branch 43 (.leaf (6)) (.leaf (1))) (.branch 45 (.leaf (0)) (.leaf (5))))) (.branch 49 (.branch 47 (.leaf (2)) (.branch 48 (.leaf (4)) (.leaf (3)))) (.branch 51 (.branch 50 (.leaf (1)) (.leaf (0))) (.branch 52 (.leaf (2)) (.leaf (7))))))))
  code := certificateD8_1737
  counts := ![(.branch 27 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 45 (.leaf (9)) (.branch 51 (.leaf (10)) (.leaf (11)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 31 (.branch 1 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-12)))) (.branch 41 (.leaf (-15)) (.branch 45 (.leaf (-17)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.leaf (-35))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (-1)) (.leaf (-2)))),
  (.branch 29 (.branch 3 (.leaf (0)) (.leaf (-19))) (.branch 42 (.leaf (-25)) (.leaf (-28)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-29)) (.leaf (-34)))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (-9)) (.leaf (-11)))),
  (.branch 15 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 46 (.leaf (-20)) (.branch 52 (.leaf (-19)) (.leaf (-17)))),
  (.branch 27 (.branch 9 (.branch 3 (.leaf (-35)) (.leaf (-34))) (.branch 15 (.leaf (-33)) (.branch 21 (.leaf (-32)) (.leaf (-31))))) (.branch 45 (.branch 33 (.leaf (-30)) (.branch 39 (.leaf (-29)) (.leaf (-28)))) (.branch 51 (.leaf (-27)) (.branch 52 (.leaf (-18)) (.leaf (-9)))))),
  (.leaf (-2)),
  (.branch 50 (.branch 43 (.leaf (-28)) (.leaf (-27))) (.branch 51 (.leaf (-22)) (.branch 52 (.leaf (-17)) (.leaf (-12))))),
  (.branch 40 (.branch 22 (.branch 13 (.leaf (-34)) (.leaf (-33))) (.branch 31 (.leaf (-32)) (.leaf (-31)))) (.branch 50 (.branch 49 (.leaf (-30)) (.leaf (-24))) (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-12)) (.leaf (-6)))))),
  (.branch 49 (.branch 47 (.branch 6 (.leaf (-17)) (.leaf (-16))) (.branch 48 (.leaf (-14)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.leaf (-4))))),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 50 (.branch 49 (.leaf (-6)) (.leaf (-5))) (.branch 51 (.leaf (-4)) (.branch 52 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 35 (.branch 16 (.leaf (-7)) (.leaf (-6))) (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-2)) (.leaf (0)))))]
def witnessD8_175_1738 : CycleWitness 8 where
  length := 53
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (7)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (6)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (5)) (.leaf (1)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (6)) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (5))) (.branch 25 (.leaf (7)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (2)) (.branch 28 (.leaf (0)) (.leaf (3)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (6)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (2)) (.branch 34 (.leaf (4)) (.leaf (5)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (3))) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 46 (.branch 42 (.branch 40 (.leaf (4)) (.branch 41 (.leaf (1)) (.leaf (6)))) (.branch 44 (.branch 43 (.leaf (7)) (.leaf (0))) (.branch 45 (.leaf (3)) (.leaf (5))))) (.branch 49 (.branch 47 (.leaf (2)) (.branch 48 (.leaf (1)) (.leaf (4)))) (.branch 51 (.branch 50 (.leaf (0)) (.leaf (3))) (.branch 52 (.leaf (2)) (.leaf (6))))))))
  code := certificateD8_1738
  counts := ![(.branch 22 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.leaf (7))))),
  (.branch 26 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 12 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 32 (.leaf (-19)) (.leaf (-23)))),
  (.branch 36 (.branch 2 (.leaf (0)) (.leaf (-29))) (.branch 41 (.leaf (-30)) (.leaf (-41)))),
  (.branch 19 (.branch 13 (.leaf (0)) (.leaf (-1))) (.branch 39 (.leaf (-2)) (.branch 52 (.leaf (-3)) (.leaf (-4))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (-5))) (.branch 51 (.leaf (-6)) (.leaf (-8)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 40 (.leaf (-6)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (-27)) (.leaf (-33)))),
  (.branch 20 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-29)) (.leaf (-31))))]
  high := ![(.branch 45 (.branch 33 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21)))) (.branch 51 (.leaf (-20)) (.branch 52 (.leaf (-17)) (.leaf (-14))))),
  (.branch 50 (.branch 42 (.leaf (-41)) (.branch 49 (.leaf (-40)) (.leaf (-34)))) (.branch 51 (.leaf (-28)) (.branch 52 (.leaf (-22)) (.leaf (-16))))),
  (.leaf (-4)),
  (.branch 52 (.leaf (-8)) (.leaf (-5))),
  (.branch 50 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4))))),
  (.branch 48 (.branch 36 (.branch 25 (.leaf (-33)) (.leaf (-32))) (.branch 47 (.leaf (-31)) (.leaf (-27)))) (.branch 50 (.branch 49 (.leaf (-23)) (.leaf (-19))) (.branch 51 (.leaf (-15)) (.branch 52 (.leaf (-11)) (.leaf (-7)))))),
  (.branch 43 (.leaf (-2)) (.branch 44 (.leaf (-1)) (.leaf (0)))),
  (.branch 47 (.branch 44 (.branch 26 (.leaf (-31)) (.leaf (-30))) (.branch 45 (.leaf (-27)) (.branch 46 (.leaf (-24)) (.leaf (-21))))) (.branch 50 (.branch 48 (.leaf (-18)) (.branch 49 (.leaf (-15)) (.leaf (-12)))) (.branch 51 (.leaf (-9)) (.branch 52 (.leaf (-6)) (.leaf (-3))))))]
def witnessD8_175_1739 : CycleWitness 8 where
  length := 53
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (1)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (4)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (6)) (.branch 21 (.leaf (4)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (5))) (.branch 25 (.leaf (0)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (7)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (4)) (.branch 31 (.leaf (0)) (.leaf (6))))) (.branch 35 (.branch 33 (.leaf (3)) (.branch 34 (.leaf (5)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (0))) (.branch 38 (.leaf (4)) (.leaf (7)))))) (.branch 46 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (3)) (.leaf (0)))) (.branch 44 (.branch 43 (.leaf (2)) (.leaf (5))) (.branch 45 (.leaf (6)) (.leaf (1))))) (.branch 49 (.branch 47 (.leaf (4)) (.branch 48 (.leaf (0)) (.leaf (3)))) (.branch 51 (.branch 50 (.leaf (2)) (.leaf (5))) (.branch 52 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_1739
  counts := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 48 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 46 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 42 (.leaf (-44)) (.leaf (-46)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-24)) (.leaf (-27)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-11)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.branch 38 (.leaf (-35)) (.leaf (-37)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (-3))) (.branch 24 (.leaf (-4)) (.branch 51 (.leaf (-9)) (.leaf (-12))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.leaf (-15))) (.branch 45 (.leaf (-17)) (.leaf (-18)))),
  (.branch 39 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 50 (.branch 43 (.leaf (-46)) (.branch 49 (.leaf (-45)) (.leaf (-36)))) (.branch 51 (.leaf (-27)) (.branch 52 (.leaf (-18)) (.leaf (-9))))),
  (.leaf (-2)),
  (.branch 37 (.branch 23 (.branch 16 (.leaf (-27)) (.leaf (-26))) (.branch 30 (.leaf (-25)) (.leaf (-24)))) (.branch 51 (.branch 44 (.leaf (-23)) (.leaf (-22))) (.branch 52 (.leaf (-17)) (.leaf (-12))))),
  (.branch 50 (.branch 34 (.leaf (-16)) (.branch 42 (.leaf (-15)) (.leaf (-14)))) (.branch 51 (.leaf (-11)) (.branch 52 (.leaf (-8)) (.leaf (-5))))),
  (.branch 49 (.branch 39 (.leaf (-37)) (.branch 48 (.leaf (-36)) (.leaf (-30)))) (.branch 51 (.branch 50 (.leaf (-24)) (.leaf (-18))) (.branch 52 (.leaf (-12)) (.leaf (-6))))),
  (.branch 52 (.leaf (-12)) (.leaf (-10))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-18)) (.leaf (-16))) (.branch 48 (.leaf (-14)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.leaf (-4))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-1)) (.leaf (0))))]
def witnessD8_175 : Fin 18 → CycleWitness 8 := ![witnessD8_175_1722, witnessD8_175_1723, witnessD8_175_1724, witnessD8_175_1725, witnessD8_175_1726, witnessD8_175_1727, witnessD8_175_1728, witnessD8_175_1729, witnessD8_175_1730, witnessD8_175_1731, witnessD8_175_1732, witnessD8_175_1733, witnessD8_175_1734, witnessD8_175_1735, witnessD8_175_1736, witnessD8_175_1737, witnessD8_175_1738, witnessD8_175_1739]
end RealPinwheel.FiveSixths


