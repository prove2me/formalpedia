-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_181
-- name    : RealPinwheel_FiveSixths_WitnessD8_181
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:32:48.442224+00:00
-- url     : https://prove2.me/theorems/e8db7e35-19cd-4114-a54f-916da09fd7b9
-- title:
--   Exact witness block D8_181
-- statement:
--   These exact witnesses represent words 1836 through 1854 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1836–1854; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_181_1835 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (4)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (1)))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (0)) (.leaf (4))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (2)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (1))) (.branch 38 (.leaf (4)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (1)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (0)) (.leaf (4))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (4)) (.leaf (7))))))))
  code := certificateD8_1835
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.branch 26 (.leaf (0)) (.leaf (-26))),
  (.leaf (0))]
  high := ![(.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 51 (.leaf (-6)) (.leaf (-3))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (-26)) (.branch 28 (.leaf (-25)) (.leaf (-24)))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-21))))) (.branch 35 (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18)))) (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_181_1836 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (7)) (.branch 18 (.leaf (0)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (3)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (1)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (1)))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (0)) (.leaf (4))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (7)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (5))) (.branch 38 (.leaf (1)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (1)))) (.branch 43 (.leaf (6)) (.branch 44 (.leaf (0)) (.leaf (4))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (3)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_1836
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-14)) (.leaf (-15)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-28))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 50 (.branch 45 (.leaf (-11)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 47 (.leaf (-5)) (.leaf (-3))),
  (.branch 49 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.branch 44 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 35 (.leaf (-2)) (.leaf (0)))]
def witnessD8_181_1837 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (6)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (7)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (6)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (4)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (7)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (5)) (.leaf (0))) (.branch 38 (.leaf (3)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (6)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (4)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (5)) (.leaf (0))) (.branch 51 (.leaf (7)) (.leaf (1))))))))
  code := certificateD8_1837
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (-28))) (.branch 42 (.leaf (-29)) (.leaf (-30)))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 47 (.leaf (-11)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 46 (.leaf (-1)) (.leaf (0))),
  (.branch 49 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 48 (.branch 30 (.leaf (-17)) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-30)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 17 (.leaf (-4)) (.leaf (-3)))]
def witnessD8_181_1838 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (2))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (5)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (7)) (.leaf (2))) (.branch 25 (.leaf (4)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (5)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (6)) (.leaf (2))) (.branch 38 (.leaf (3)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (4)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (7)) (.leaf (2))) (.branch 51 (.leaf (5)) (.leaf (1))))))))
  code := certificateD8_1838
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-4)) (.leaf (-5)))),
  (.branch 10 (.leaf (0)) (.leaf (-16))),
  (.branch 23 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 48 (.leaf (-2)) (.leaf (0))),
  (.branch 46 (.leaf (-8)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 46 (.branch 43 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 34 (.leaf (-5)) (.leaf (-3))),
  (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_181_1839 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (5)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (6)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (2))) (.branch 25 (.leaf (7)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (5)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (6)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (2))) (.branch 38 (.leaf (4)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (7)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (5)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (2))) (.branch 51 (.leaf (6)) (.leaf (1))))))))
  code := certificateD8_1839
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-43)) (.leaf (-44)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (-16))) (.branch 46 (.leaf (-17)) (.leaf (-18)))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-31)))]
  high := ![(.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 48 (.leaf (-2)) (.leaf (0))),
  (.branch 46 (.leaf (-8)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 44 (.branch 40 (.branch 21 (.leaf (-44)) (.branch 39 (.leaf (-42)) (.leaf (-39)))) (.branch 42 (.branch 41 (.leaf (-36)) (.leaf (-33))) (.branch 43 (.leaf (-30)) (.leaf (-27))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-24)) (.leaf (-21))) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.leaf (-5)) (.leaf (-3))),
  (.branch 46 (.branch 43 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))))]
def witnessD8_181_1840 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (7)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (6)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (4)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (3)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (7)) (.branch 34 (.leaf (2)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (0))) (.branch 38 (.leaf (4)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (2)) (.leaf (6)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (7)) (.leaf (5))))))))
  code := certificateD8_1840
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-21))) (.branch 11 (.leaf (-22)) (.leaf (-23)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))) (.branch 19 (.leaf (-8)) (.branch 24 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-2)) (.leaf (-4)))) (.branch 36 (.leaf (-5)) (.branch 49 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 49 (.branch 38 (.leaf (-23)) (.leaf (-20))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 51 (.leaf (-10)) (.leaf (-5))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 46 (.branch 43 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 34 (.leaf (-5)) (.leaf (-3)))]
def witnessD8_181_1841 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (3)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (5))) (.branch 12 (.leaf (3)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (7)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (1)) (.branch 28 (.leaf (2)) (.leaf (5)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (6))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (4)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (5))) (.branch 38 (.leaf (3)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (7)) (.branch 41 (.leaf (2)) (.leaf (0)))) (.branch 43 (.leaf (4)) (.branch 44 (.leaf (3)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (5)) (.branch 47 (.leaf (0)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (6)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (4))))))))
  code := certificateD8_1841
  counts := ![(.branch 24 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 45 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 24 (.branch 1 (.leaf (0)) (.leaf (-43))) (.branch 47 (.leaf (-44)) (.leaf (-45)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-16)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-19)))),
  (.branch 14 (.leaf (0)) (.leaf (-10))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (-34))) (.branch 40 (.leaf (-35)) (.leaf (-36))))]
  high := ![(.branch 49 (.branch 48 (.leaf (-45)) (.leaf (-36))) (.branch 50 (.leaf (-27)) (.branch 51 (.leaf (-18)) (.leaf (-9))))),
  (.branch 22 (.leaf (-19)) (.branch 51 (.leaf (-18)) (.leaf (-9)))),
  (.branch 49 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 45 (.leaf (-3)) (.leaf (-2))),
  (.branch 35 (.leaf (-2)) (.branch 44 (.leaf (-1)) (.leaf (0)))),
  (.branch 48 (.branch 38 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 50 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 46 (.branch 43 (.branch 41 (.leaf (-36)) (.branch 42 (.leaf (-33)) (.leaf (-30)))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))))]
def witnessD8_181_1842 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (2)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (3))) (.branch 12 (.leaf (2)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (7)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (4))) (.branch 25 (.leaf (6)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (3)) (.leaf (2)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (4))))) (.branch 35 (.branch 33 (.leaf (7)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (5)) (.leaf (3))) (.branch 38 (.leaf (2)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (4)) (.leaf (6)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (5)) (.leaf (4))) (.branch 51 (.leaf (7)) (.leaf (1))))))))
  code := certificateD8_1842
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-20)) (.leaf (-21)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 48 (.leaf (-2)) (.leaf (0))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 42 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 43 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 34 (.leaf (-5)) (.leaf (-3)))]
def witnessD8_181_1843 : CycleWitness 8 where
  length := 51
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 20 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (4)))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (0))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (6)) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (3))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (4)) (.leaf (0))) (.branch 42 (.leaf (2)) (.branch 43 (.leaf (0)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (7)) (.leaf (0)))) (.branch 49 (.leaf (1)) (.branch 50 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_1843
  counts := ![(.branch 24 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 14 (.branch 12 (.leaf (7)) (.leaf (8))) (.branch 16 (.leaf (9)) (.leaf (10)))) (.branch 20 (.branch 19 (.leaf (11)) (.leaf (12))) (.branch 22 (.leaf (13)) (.leaf (14)))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (15)) (.leaf (16))) (.branch 29 (.leaf (17)) (.leaf (18)))) (.branch 35 (.branch 33 (.leaf (19)) (.leaf (20))) (.branch 36 (.leaf (21)) (.leaf (22))))) (.branch 45 (.branch 41 (.branch 39 (.leaf (23)) (.leaf (24))) (.branch 43 (.leaf (25)) (.leaf (26)))) (.branch 48 (.branch 46 (.leaf (27)) (.leaf (28))) (.branch 50 (.leaf (29)) (.leaf (30))))))),
  (.branch 27 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 49 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 20 (.leaf (-9)) (.branch 37 (.leaf (-11)) (.leaf (-13))))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-38))),
  (.branch 30 (.leaf (0)) (.leaf (-21))),
  (.branch 47 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 47 (.branch 38 (.leaf (-13)) (.leaf (-12))) (.branch 49 (.leaf (-11)) (.leaf (-10)))),
  (.branch 50 (.leaf (-6)) (.leaf (-3))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 45 (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-38)) (.leaf (-37))) (.branch 16 (.leaf (-36)) (.leaf (-35)))) (.branch 19 (.branch 18 (.leaf (-34)) (.leaf (-33))) (.branch 20 (.leaf (-32)) (.branch 21 (.leaf (-31)) (.leaf (-30)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-29)) (.leaf (-28))) (.branch 25 (.leaf (-27)) (.branch 26 (.leaf (-26)) (.leaf (-25))))) (.branch 29 (.branch 28 (.leaf (-24)) (.leaf (-23))) (.branch 30 (.leaf (-22)) (.branch 31 (.leaf (-21)) (.leaf (-20))))))) (.branch 41 (.branch 36 (.branch 34 (.branch 33 (.leaf (-19)) (.leaf (-18))) (.branch 35 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 35 (.branch 32 (.branch 31 (.leaf (-21)) (.leaf (-20))) (.branch 33 (.leaf (-19)) (.branch 34 (.leaf (-18)) (.leaf (-17))))) (.branch 37 (.branch 36 (.leaf (-16)) (.leaf (-15))) (.branch 38 (.leaf (-14)) (.branch 39 (.leaf (-13)) (.leaf (-12)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_181_1844 : CycleWitness 8 where
  length := 51
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 11 (.leaf (3)) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (5)) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (0)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (3)) (.leaf (0)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (6)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (4)) (.leaf (0)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 49 (.leaf (1)) (.branch 50 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_1844
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))) (.branch 21 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 23 (.leaf (12)) (.leaf (13)))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (14)) (.branch 29 (.leaf (15)) (.leaf (16)))) (.branch 35 (.branch 33 (.leaf (17)) (.leaf (18))) (.branch 36 (.leaf (19)) (.leaf (20))))) (.branch 44 (.branch 40 (.leaf (21)) (.branch 42 (.leaf (22)) (.leaf (23)))) (.branch 48 (.branch 46 (.leaf (24)) (.leaf (25))) (.branch 50 (.leaf (26)) (.leaf (27))))))),
  (.branch 26 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 43 (.leaf (7)) (.branch 49 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 51 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-34))),
  (.branch 34 (.leaf (0)) (.leaf (-17))),
  (.leaf (0))]
  high := ![(.branch 43 (.branch 39 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 47 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 49 (.leaf (-10)) (.leaf (-9))))),
  (.branch 44 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 50 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (-34)) (.leaf (-33))) (.branch 20 (.leaf (-32)) (.leaf (-31)))) (.branch 23 (.branch 22 (.leaf (-30)) (.leaf (-29))) (.branch 24 (.leaf (-28)) (.leaf (-27))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-26)) (.leaf (-25))) (.branch 28 (.leaf (-24)) (.leaf (-23)))) (.branch 31 (.branch 30 (.leaf (-22)) (.leaf (-21))) (.branch 32 (.leaf (-20)) (.branch 33 (.leaf (-19)) (.leaf (-18))))))) (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (-17)) (.leaf (-16))) (.branch 37 (.leaf (-15)) (.leaf (-14)))) (.branch 40 (.branch 39 (.leaf (-13)) (.leaf (-12))) (.branch 41 (.leaf (-11)) (.leaf (-10))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (-17)) (.leaf (-16))) (.branch 37 (.leaf (-15)) (.leaf (-14)))) (.branch 40 (.branch 39 (.leaf (-13)) (.leaf (-12))) (.branch 41 (.leaf (-11)) (.leaf (-10))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_181_1845 : CycleWitness 8 where
  length := 51
  word := (.branch 26 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.leaf (0))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (4))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (6)) (.leaf (0))))))) (.branch 38 (.branch 32 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (4))))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (0)))))) (.branch 44 (.branch 40 (.branch 39 (.leaf (3)) (.leaf (0))) (.branch 41 (.leaf (7)) (.branch 43 (.leaf (0)) (.leaf (2))))) (.branch 48 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (0)))) (.branch 49 (.leaf (4)) (.branch 50 (.leaf (0)) (.leaf (2))))))))
  code := certificateD8_1845
  counts := ![(.branch 25 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 14 (.branch 13 (.leaf (7)) (.leaf (8))) (.branch 16 (.leaf (9)) (.leaf (10)))) (.branch 21 (.branch 19 (.leaf (11)) (.leaf (12))) (.branch 23 (.leaf (13)) (.leaf (14)))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (15)) (.leaf (16))) (.branch 30 (.leaf (17)) (.leaf (18)))) (.branch 35 (.branch 33 (.leaf (19)) (.leaf (20))) (.branch 36 (.leaf (21)) (.leaf (22))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (23)) (.leaf (24))) (.branch 43 (.leaf (25)) (.leaf (26)))) (.branch 48 (.branch 47 (.leaf (27)) (.leaf (28))) (.branch 50 (.leaf (29)) (.leaf (30))))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-44))),
  (.branch 24 (.leaf (0)) (.leaf (-27))),
  (.branch 41 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 37 (.leaf (-14)) (.branch 49 (.leaf (-13)) (.leaf (-10)))),
  (.branch 48 (.branch 38 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 35 (.leaf (-2)) (.branch 45 (.leaf (-1)) (.leaf (0)))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.leaf (-2)) (.leaf (-1))),
  (.branch 29 (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-44)) (.leaf (-43))) (.branch 10 (.leaf (-42)) (.branch 11 (.leaf (-41)) (.leaf (-40))))) (.branch 15 (.branch 13 (.leaf (-39)) (.branch 14 (.leaf (-38)) (.leaf (-37)))) (.branch 16 (.leaf (-36)) (.branch 17 (.leaf (-35)) (.leaf (-34)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-33)) (.leaf (-32))) (.branch 21 (.leaf (-31)) (.branch 22 (.leaf (-30)) (.leaf (-29))))) (.branch 26 (.branch 24 (.leaf (-28)) (.branch 25 (.leaf (-27)) (.leaf (-26)))) (.branch 27 (.leaf (-25)) (.branch 28 (.leaf (-24)) (.leaf (-23))))))) (.branch 40 (.branch 34 (.branch 31 (.branch 30 (.leaf (-22)) (.leaf (-21))) (.branch 32 (.leaf (-20)) (.branch 33 (.leaf (-19)) (.leaf (-18))))) (.branch 37 (.branch 35 (.leaf (-17)) (.branch 36 (.leaf (-16)) (.leaf (-15)))) (.branch 38 (.leaf (-14)) (.branch 39 (.leaf (-13)) (.leaf (-12)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 37 (.branch 30 (.branch 27 (.branch 25 (.leaf (-27)) (.branch 26 (.leaf (-26)) (.leaf (-25)))) (.branch 28 (.leaf (-24)) (.branch 29 (.leaf (-23)) (.leaf (-22))))) (.branch 33 (.branch 31 (.leaf (-21)) (.branch 32 (.leaf (-20)) (.leaf (-19)))) (.branch 35 (.branch 34 (.leaf (-18)) (.leaf (-17))) (.branch 36 (.leaf (-16)) (.leaf (-15)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (-14)) (.branch 39 (.leaf (-13)) (.leaf (-12)))) (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.leaf (-8))))) (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_181_1846 : CycleWitness 8 where
  length := 51
  word := (.branch 25 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (5)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 11 (.leaf (7)) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 23 (.leaf (6)) (.branch 24 (.leaf (0)) (.leaf (4))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 32 (.leaf (5)) (.branch 34 (.leaf (0)) (.leaf (7)))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (4)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (2)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 42 (.leaf (3)) (.branch 43 (.leaf (0)) (.leaf (5))))) (.branch 47 (.branch 45 (.leaf (1)) (.branch 46 (.leaf (0)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (6)) (.leaf (0))) (.branch 50 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_1846
  counts := ![(.branch 24 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 33 (.leaf (12)) (.branch 34 (.leaf (13)) (.leaf (14))))) (.branch 43 (.branch 40 (.leaf (15)) (.leaf (16))) (.branch 46 (.leaf (17)) (.branch 49 (.leaf (18)) (.leaf (19))))))),
  (.branch 26 (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 45 (.leaf (9)) (.branch 50 (.leaf (10)) (.leaf (11)))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-13)) (.leaf (-26)))) (.branch 12 (.leaf (-30)) (.branch 34 (.leaf (-36)) (.leaf (-42))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 26 (.leaf (-10)) (.branch 45 (.leaf (-14)) (.leaf (-15))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (-7))) (.branch 47 (.leaf (-8)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-39))),
  (.branch 25 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.branch 44 (.leaf (-7)) (.leaf (-8)))),
  (.branch 23 (.leaf (0)) (.branch 48 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.leaf (0)) (.branch 35 (.leaf (-15)) (.leaf (-17))))]
  high := ![(.branch 41 (.branch 35 (.leaf (-42)) (.branch 38 (.leaf (-41)) (.leaf (-40)))) (.branch 47 (.branch 44 (.leaf (-39)) (.leaf (-38))) (.branch 50 (.leaf (-37)) (.leaf (-30))))),
  (.branch 46 (.leaf (-15)) (.leaf (-14))),
  (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-9))) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.branch 45 (.branch 30 (.branch 4 (.leaf (-39)) (.branch 17 (.leaf (-38)) (.leaf (-37)))) (.branch 43 (.leaf (-36)) (.branch 44 (.leaf (-32)) (.leaf (-28))))) (.branch 48 (.branch 46 (.leaf (-24)) (.branch 47 (.leaf (-20)) (.leaf (-16)))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 26 (.leaf (-2)) (.branch 39 (.leaf (-1)) (.leaf (0)))),
  (.branch 47 (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.leaf (-2))))),
  (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.leaf (-2))))))]
def witnessD8_181_1847 : CycleWitness 8 where
  length := 51
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (2)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 11 (.leaf (5)) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 17 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (4))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (0)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (6)) (.leaf (0)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (2)) (.leaf (0))))) (.branch 36 (.branch 33 (.leaf (3)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.leaf (4)) (.branch 38 (.leaf (1)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (0)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (7))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (3)) (.leaf (1))))))))
  code := certificateD8_1847
  counts := ![(.branch 25 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 12 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 19 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))) (.branch 36 (.branch 29 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.branch 35 (.leaf (14)) (.leaf (15))))) (.branch 44 (.branch 39 (.leaf (16)) (.branch 42 (.leaf (17)) (.leaf (18)))) (.branch 46 (.leaf (19)) (.branch 49 (.leaf (20)) (.leaf (21))))))),
  (.branch 26 (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.branch 36 (.leaf (-7)) (.leaf (-8))))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 11 (.leaf (0)) (.leaf (-40))),
  (.branch 28 (.leaf (0)) (.leaf (-23))),
  (.branch 45 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 47 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.branch 39 (.leaf (-1)) (.leaf (0))),
  (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))),
  (.branch 42 (.leaf (-3)) (.leaf (-2))),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-14)) (.branch 39 (.leaf (-13)) (.leaf (-12)))) (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.leaf (-8))))) (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-40)) (.leaf (-39))) (.branch 14 (.leaf (-38)) (.branch 15 (.leaf (-37)) (.leaf (-36))))) (.branch 18 (.branch 17 (.leaf (-35)) (.leaf (-34))) (.branch 19 (.leaf (-33)) (.branch 20 (.leaf (-32)) (.leaf (-31)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-30)) (.leaf (-29))) (.branch 24 (.leaf (-28)) (.branch 25 (.leaf (-27)) (.leaf (-26))))) (.branch 28 (.branch 27 (.leaf (-25)) (.leaf (-24))) (.branch 29 (.leaf (-23)) (.branch 30 (.leaf (-22)) (.leaf (-21))))))) (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-20)) (.leaf (-19))) (.branch 34 (.leaf (-18)) (.branch 35 (.leaf (-17)) (.leaf (-16))))) (.branch 38 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 39 (.branch 33 (.branch 30 (.branch 29 (.leaf (-23)) (.leaf (-22))) (.branch 31 (.leaf (-21)) (.branch 32 (.leaf (-20)) (.leaf (-19))))) (.branch 36 (.branch 34 (.leaf (-18)) (.branch 35 (.leaf (-17)) (.leaf (-16)))) (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_181_1848 : CycleWitness 8 where
  length := 51
  word := (.branch 25 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (2)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 11 (.leaf (6)) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (4)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 23 (.leaf (5)) (.branch 24 (.leaf (0)) (.leaf (2))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 32 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (7)))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (2)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (3)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 42 (.leaf (4)) (.branch 43 (.leaf (0)) (.leaf (2))))) (.branch 47 (.branch 45 (.leaf (1)) (.branch 46 (.leaf (0)) (.leaf (3)))) (.branch 49 (.branch 48 (.leaf (5)) (.leaf (0))) (.branch 50 (.leaf (1)) (.leaf (2))))))))
  code := certificateD8_1848
  counts := ![(.branch 24 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 33 (.leaf (12)) (.branch 34 (.leaf (13)) (.leaf (14))))) (.branch 43 (.branch 40 (.leaf (15)) (.leaf (16))) (.branch 46 (.leaf (17)) (.branch 49 (.leaf (18)) (.leaf (19))))))),
  (.branch 26 (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 45 (.leaf (9)) (.branch 50 (.leaf (10)) (.leaf (11)))))),
  (.branch 25 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-13)) (.leaf (-26)))) (.branch 12 (.leaf (-30)) (.branch 34 (.leaf (-36)) (.leaf (-42))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 26 (.leaf (-10)) (.branch 45 (.leaf (-14)) (.leaf (-15))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 44 (.leaf (-2)) (.leaf (-3)))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (-7))) (.branch 47 (.leaf (-8)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-39))),
  (.branch 23 (.leaf (0)) (.branch 48 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.leaf (0)) (.leaf (-40))),
  (.branch 35 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 41 (.branch 35 (.leaf (-42)) (.branch 38 (.leaf (-41)) (.leaf (-40)))) (.branch 47 (.branch 44 (.leaf (-39)) (.leaf (-38))) (.branch 50 (.leaf (-37)) (.leaf (-30))))),
  (.branch 46 (.leaf (-15)) (.leaf (-14))),
  (.branch 45 (.leaf (-3)) (.branch 46 (.leaf (-1)) (.leaf (0)))),
  (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-9))) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.branch 45 (.branch 30 (.branch 4 (.leaf (-39)) (.branch 17 (.leaf (-38)) (.leaf (-37)))) (.branch 43 (.leaf (-36)) (.branch 44 (.leaf (-32)) (.leaf (-28))))) (.branch 48 (.branch 46 (.leaf (-24)) (.branch 47 (.leaf (-20)) (.leaf (-16)))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))),
  (.branch 31 (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-40)) (.leaf (-39))) (.branch 14 (.leaf (-38)) (.branch 15 (.leaf (-37)) (.leaf (-36))))) (.branch 18 (.branch 17 (.leaf (-35)) (.leaf (-34))) (.branch 19 (.leaf (-33)) (.branch 20 (.leaf (-32)) (.leaf (-31)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-30)) (.leaf (-29))) (.branch 24 (.leaf (-28)) (.branch 25 (.leaf (-27)) (.leaf (-26))))) (.branch 28 (.branch 27 (.leaf (-25)) (.leaf (-24))) (.branch 29 (.leaf (-23)) (.branch 30 (.leaf (-22)) (.leaf (-21))))))) (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-20)) (.leaf (-19))) (.branch 34 (.leaf (-18)) (.branch 35 (.leaf (-17)) (.leaf (-16))))) (.branch 38 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-16)) (.leaf (-15))) (.branch 38 (.leaf (-14)) (.leaf (-13)))) (.branch 41 (.branch 40 (.leaf (-12)) (.leaf (-11))) (.branch 42 (.leaf (-10)) (.leaf (-9))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-8)) (.leaf (-7))) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_181_1849 : CycleWitness 8 where
  length := 51
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (6)) (.leaf (3)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 11 (.leaf (7)) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 19 (.leaf (0)) (.leaf (6))))) (.branch 23 (.branch 21 (.leaf (4)) (.branch 22 (.leaf (0)) (.leaf (1)))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (7)) (.leaf (0)))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (1)) (.leaf (0))))) (.branch 36 (.branch 33 (.leaf (2)) (.branch 34 (.leaf (4)) (.leaf (0)))) (.branch 37 (.leaf (6)) (.branch 38 (.leaf (5)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (2)) (.leaf (0)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (0)) (.leaf (7))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (1)))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_1849
  counts := ![(.branch 25 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 12 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 19 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))) (.branch 36 (.branch 29 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.branch 35 (.leaf (14)) (.leaf (15))))) (.branch 44 (.branch 39 (.leaf (16)) (.branch 42 (.leaf (17)) (.leaf (18)))) (.branch 46 (.leaf (19)) (.branch 49 (.leaf (20)) (.leaf (21))))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.branch 36 (.leaf (-7)) (.leaf (-8))))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-35))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (-15)) (.leaf (-18)))),
  (.branch 38 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 47 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))),
  (.branch 42 (.leaf (-3)) (.leaf (-2))),
  (.branch 45 (.branch 18 (.branch 5 (.leaf (-35)) (.leaf (-34))) (.branch 31 (.leaf (-33)) (.branch 44 (.leaf (-32)) (.leaf (-28))))) (.branch 48 (.branch 46 (.leaf (-24)) (.branch 47 (.leaf (-20)) (.leaf (-16)))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 48 (.branch 22 (.leaf (-18)) (.branch 35 (.leaf (-17)) (.leaf (-16)))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4))))),
  (.branch 39 (.leaf (-1)) (.leaf (0))),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-14)) (.branch 39 (.leaf (-13)) (.leaf (-12)))) (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.leaf (-8))))) (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_181_1850 : CycleWitness 8 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (0)) (.leaf (7)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (6))) (.branch 24 (.leaf (0)) (.leaf (4))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (5)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (7)) (.branch 33 (.leaf (0)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (0)) (.leaf (4)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (6)) (.leaf (0)))) (.branch 42 (.leaf (2)) (.branch 43 (.leaf (0)) (.leaf (1))))) (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (3)) (.leaf (5)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (7))) (.branch 50 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_1850
  counts := ![(.branch 24 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 20 (.leaf (9)) (.branch 22 (.leaf (10)) (.leaf (11)))))) (.branch 37 (.branch 31 (.branch 26 (.leaf (12)) (.branch 28 (.leaf (13)) (.leaf (14)))) (.branch 33 (.leaf (15)) (.branch 35 (.leaf (16)) (.leaf (17))))) (.branch 43 (.branch 39 (.leaf (18)) (.branch 41 (.leaf (19)) (.leaf (20)))) (.branch 48 (.branch 45 (.leaf (21)) (.leaf (22))) (.branch 50 (.leaf (23)) (.leaf (24))))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-10)))) (.branch 9 (.branch 7 (.leaf (-11)) (.leaf (-12))) (.branch 11 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-35)) (.leaf (-37)))),
  (.branch 8 (.leaf (0)) (.branch 46 (.leaf (-19)) (.leaf (-20)))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 13 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 46 (.leaf (-14)) (.leaf (-8))),
  (.branch 47 (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 46 (.branch 43 (.branch 30 (.leaf (-37)) (.leaf (-36))) (.branch 44 (.leaf (-32)) (.branch 45 (.leaf (-28)) (.leaf (-24))))) (.branch 48 (.branch 47 (.leaf (-20)) (.leaf (-16))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 48 (.branch 47 (.leaf (-20)) (.leaf (-16))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4))))),
  (.branch 26 (.branch 13 (.leaf (-3)) (.leaf (-2))) (.branch 39 (.leaf (-1)) (.leaf (0)))),
  (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_181_1851 : CycleWitness 8 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (0)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (3))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (6)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (2)) (.branch 33 (.leaf (0)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (0)) (.leaf (4)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 42 (.leaf (3)) (.branch 43 (.leaf (0)) (.leaf (1))))) (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (4)) (.leaf (7)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (2))) (.branch 50 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_1851
  counts := ![(.branch 24 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 20 (.leaf (9)) (.branch 22 (.leaf (10)) (.leaf (11)))))) (.branch 37 (.branch 31 (.branch 26 (.leaf (12)) (.branch 28 (.leaf (13)) (.leaf (14)))) (.branch 33 (.leaf (15)) (.branch 35 (.leaf (16)) (.leaf (17))))) (.branch 43 (.branch 39 (.leaf (18)) (.branch 41 (.leaf (19)) (.leaf (20)))) (.branch 48 (.branch 45 (.leaf (21)) (.leaf (22))) (.branch 50 (.leaf (23)) (.leaf (24))))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-10)))) (.branch 9 (.branch 7 (.leaf (-11)) (.leaf (-12))) (.branch 11 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 13 (.leaf (0)) (.leaf (-38))),
  (.branch 30 (.leaf (0)) (.leaf (-21))),
  (.branch 47 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 46 (.leaf (-14)) (.leaf (-8))),
  (.branch 47 (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 41 (.leaf (-5)) (.branch 50 (.leaf (-4)) (.leaf (-2)))),
  (.branch 43 (.leaf (-1)) (.leaf (0))),
  (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 32 (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-38)) (.leaf (-37))) (.branch 16 (.leaf (-36)) (.leaf (-35)))) (.branch 19 (.branch 18 (.leaf (-34)) (.leaf (-33))) (.branch 20 (.leaf (-32)) (.branch 21 (.leaf (-31)) (.leaf (-30)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-29)) (.leaf (-28))) (.branch 25 (.leaf (-27)) (.branch 26 (.leaf (-26)) (.leaf (-25))))) (.branch 29 (.branch 28 (.leaf (-24)) (.leaf (-23))) (.branch 30 (.leaf (-22)) (.branch 31 (.leaf (-21)) (.leaf (-20))))))) (.branch 41 (.branch 36 (.branch 34 (.branch 33 (.leaf (-19)) (.leaf (-18))) (.branch 35 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 35 (.branch 32 (.branch 31 (.leaf (-21)) (.leaf (-20))) (.branch 33 (.leaf (-19)) (.branch 34 (.leaf (-18)) (.leaf (-17))))) (.branch 37 (.branch 36 (.leaf (-16)) (.leaf (-15))) (.branch 38 (.leaf (-14)) (.branch 39 (.leaf (-13)) (.leaf (-12)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_181_1852 : CycleWitness 8 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (5)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (3)) (.leaf (0)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (1))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (6)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (3))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (4)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (0)) (.leaf (4)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 42 (.leaf (1)) (.branch 43 (.leaf (2)) (.leaf (0))))) (.branch 47 (.branch 45 (.leaf (7)) (.branch 46 (.leaf (0)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (3)) (.leaf (0))) (.branch 50 (.leaf (4)) (.leaf (2))))))))
  code := certificateD8_1852
  counts := ![(.branch 24 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 12 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))) (.branch 37 (.branch 29 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.branch 35 (.leaf (14)) (.leaf (15))))) (.branch 44 (.branch 39 (.leaf (16)) (.branch 41 (.leaf (17)) (.leaf (18)))) (.branch 46 (.leaf (19)) (.branch 49 (.leaf (20)) (.leaf (21))))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))) (.branch 24 (.branch 7 (.leaf (-5)) (.leaf (-6))) (.branch 41 (.leaf (-7)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 38 (.leaf (-12)) (.leaf (-17)))),
  (.branch 11 (.leaf (0)) (.leaf (-40))),
  (.branch 28 (.leaf (0)) (.leaf (-23))),
  (.branch 45 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 47 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.branch 49 (.branch 48 (.leaf (-12)) (.leaf (-9))) (.branch 50 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))),
  (.branch 39 (.leaf (-17)) (.leaf (-16))),
  (.branch 31 (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-40)) (.leaf (-39))) (.branch 14 (.leaf (-38)) (.branch 15 (.leaf (-37)) (.leaf (-36))))) (.branch 18 (.branch 17 (.leaf (-35)) (.leaf (-34))) (.branch 19 (.leaf (-33)) (.branch 20 (.leaf (-32)) (.leaf (-31)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-30)) (.leaf (-29))) (.branch 24 (.leaf (-28)) (.branch 25 (.leaf (-27)) (.leaf (-26))))) (.branch 28 (.branch 27 (.leaf (-25)) (.leaf (-24))) (.branch 29 (.leaf (-23)) (.branch 30 (.leaf (-22)) (.leaf (-21))))))) (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-20)) (.leaf (-19))) (.branch 34 (.leaf (-18)) (.branch 35 (.leaf (-17)) (.leaf (-16))))) (.branch 38 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 39 (.branch 33 (.branch 30 (.branch 29 (.leaf (-23)) (.leaf (-22))) (.branch 31 (.leaf (-21)) (.branch 32 (.leaf (-20)) (.leaf (-19))))) (.branch 36 (.branch 34 (.leaf (-18)) (.branch 35 (.leaf (-17)) (.leaf (-16)))) (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_181_1853 : CycleWitness 8 where
  length := 51
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (4)) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (2)) (.leaf (5)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (4)) (.leaf (2)))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (6)) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (2)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (0)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (7)) (.leaf (0)))) (.branch 49 (.leaf (1)) (.branch 50 (.leaf (2)) (.leaf (3))))))))
  code := certificateD8_1853
  counts := ![(.branch 25 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.leaf (15)))))),
  (.branch 24 (.branch 11 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.leaf (15)))))),
  (.branch 29 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 46 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))) (.branch 27 (.leaf (-8)) (.branch 44 (.leaf (-9)) (.leaf (-10))))),
  (.branch 3 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 20 (.leaf (-18)) (.branch 37 (.leaf (-25)) (.leaf (-32))))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (-2))) (.branch 50 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-38))),
  (.branch 30 (.leaf (0)) (.leaf (-21))),
  (.branch 47 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 49 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.branch 42 (.branch 38 (.leaf (-32)) (.leaf (-31))) (.branch 46 (.leaf (-30)) (.branch 50 (.leaf (-29)) (.leaf (-25))))),
  (.leaf (-4)),
  (.leaf (0)),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-38)) (.leaf (-37))) (.branch 16 (.leaf (-36)) (.leaf (-35)))) (.branch 19 (.branch 18 (.leaf (-34)) (.leaf (-33))) (.branch 20 (.leaf (-32)) (.branch 21 (.leaf (-31)) (.leaf (-30)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-29)) (.leaf (-28))) (.branch 25 (.leaf (-27)) (.branch 26 (.leaf (-26)) (.leaf (-25))))) (.branch 29 (.branch 28 (.leaf (-24)) (.leaf (-23))) (.branch 30 (.leaf (-22)) (.branch 31 (.leaf (-21)) (.leaf (-20))))))) (.branch 41 (.branch 36 (.branch 34 (.branch 33 (.leaf (-19)) (.leaf (-18))) (.branch 35 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 35 (.branch 32 (.branch 31 (.leaf (-21)) (.leaf (-20))) (.branch 33 (.leaf (-19)) (.branch 34 (.leaf (-18)) (.leaf (-17))))) (.branch 37 (.branch 36 (.leaf (-16)) (.leaf (-15))) (.branch 38 (.leaf (-14)) (.branch 39 (.leaf (-13)) (.leaf (-12)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_181 : Fin 19 → CycleWitness 8 := ![witnessD8_181_1835, witnessD8_181_1836, witnessD8_181_1837, witnessD8_181_1838, witnessD8_181_1839, witnessD8_181_1840, witnessD8_181_1841, witnessD8_181_1842, witnessD8_181_1843, witnessD8_181_1844, witnessD8_181_1845, witnessD8_181_1846, witnessD8_181_1847, witnessD8_181_1848, witnessD8_181_1849, witnessD8_181_1850, witnessD8_181_1851, witnessD8_181_1852, witnessD8_181_1853]
end RealPinwheel.FiveSixths


