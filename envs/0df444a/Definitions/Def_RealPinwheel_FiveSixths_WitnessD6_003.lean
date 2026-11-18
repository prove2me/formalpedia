-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_003
-- name    : RealPinwheel_FiveSixths_WitnessD6_003
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:06:22.901321+00:00
-- url     : https://prove2.me/theorems/00763252-dca0-4520-a0c5-d4e81fad6a6c
-- title:
--   Exact witness block D6_003
-- statement:
--   These exact witnesses represent words 57 through 79 of source certificate file D6. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D6, entries 57–79; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D6.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD6
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD6_003_56 : CycleWitness 6 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (4)) (.leaf (0)))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (5)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 20 (.leaf (3)) (.branch 21 (.leaf (0)) (.leaf (4))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (5)) (.leaf (0)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (2)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (4)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 42 (.leaf (3)) (.branch 43 (.leaf (0)) (.leaf (5))))))))
  code := certificateD6_56
  counts := ![(.branch 21 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 16 (.leaf (7)) (.branch 19 (.leaf (8)) (.leaf (9)))))) (.branch 32 (.branch 25 (.branch 23 (.leaf (10)) (.leaf (11))) (.branch 27 (.leaf (12)) (.branch 30 (.leaf (13)) (.leaf (14))))) (.branch 38 (.branch 34 (.leaf (15)) (.branch 36 (.leaf (16)) (.leaf (17)))) (.branch 41 (.leaf (18)) (.branch 43 (.leaf (19)) (.leaf (20))))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-4)) (.leaf (-6)))) (.branch 28 (.leaf (-7)) (.branch 39 (.leaf (-8)) (.leaf (-9))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 18 (.leaf (-11)) (.leaf (-12)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 29 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 39 (.leaf (-8)) (.leaf (-5))),
  (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5))))),
  (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 43 (.leaf (-2)) (.leaf (-1))),
  (.branch 39 (.branch 23 (.branch 8 (.leaf (-23)) (.leaf (-22))) (.branch 38 (.leaf (-21)) (.leaf (-18)))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 30 (.leaf (-1)) (.leaf (0)))]
def witnessD6_003_57 : CycleWitness 6 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (4))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (1)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (4)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (1))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (5))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (1)) (.leaf (0)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (4)) (.leaf (0))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (2)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (0)) (.leaf (5)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (3)) (.leaf (1))))))))
  code := certificateD6_57
  counts := ![(.branch 20 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))) (.branch 33 (.branch 25 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.branch 30 (.leaf (12)) (.leaf (13))))) (.branch 38 (.branch 35 (.leaf (14)) (.leaf (15))) (.branch 40 (.leaf (16)) (.branch 42 (.leaf (17)) (.leaf (18))))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 24 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 17 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 24 (.leaf (-3)) (.branch 39 (.leaf (-4)) (.leaf (-5))))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-29)) (.leaf (-31)))),
  (.branch 12 (.leaf (0)) (.branch 41 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 43 (.leaf (-18)) (.leaf (-9))),
  (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.leaf (-2)) (.leaf (-1))),
  (.branch 38 (.branch 35 (.branch 20 (.leaf (-31)) (.leaf (-30))) (.branch 36 (.leaf (-27)) (.branch 37 (.leaf (-24)) (.leaf (-21))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-15)) (.leaf (-12)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))]
def witnessD6_003_58 : CycleWitness 6 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (4))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (3)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (5))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (5))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (0)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (1)) (.leaf (4))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (3)) (.leaf (1)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (5)) (.leaf (2))))))))
  code := certificateD6_58
  counts := ![(.branch 20 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 31 (.branch 25 (.branch 23 (.leaf (8)) (.leaf (9))) (.branch 28 (.leaf (10)) (.leaf (11)))) (.branch 36 (.branch 33 (.leaf (12)) (.leaf (13))) (.branch 39 (.leaf (14)) (.branch 42 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 24 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 11 (.leaf (-10)) (.leaf (-11)))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-11)))) (.branch 37 (.leaf (-13)) (.branch 41 (.leaf (-15)) (.leaf (-17))))),
  (.branch 4 (.leaf (0)) (.branch 26 (.leaf (-5)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 37 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-4))))),
  (.branch 42 (.leaf (-17)) (.branch 43 (.leaf (-14)) (.leaf (-11)))),
  (.branch 33 (.branch 27 (.leaf (-7)) (.leaf (-6))) (.branch 39 (.leaf (-5)) (.branch 40 (.leaf (-2)) (.leaf (0))))),
  (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.leaf (-7)))) (.branch 41 (.branch 40 (.leaf (-6)) (.leaf (-5))) (.branch 42 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 28 (.leaf (-3)) (.leaf (-2)))]
def witnessD6_003_59 : CycleWitness 6 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (3)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (4)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (3)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (2)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 37 (.leaf (0)) (.leaf (1))))) (.branch 41 (.branch 39 (.leaf (2)) (.branch 40 (.leaf (0)) (.leaf (5)))) (.branch 42 (.leaf (1)) (.branch 43 (.leaf (0)) (.leaf (2))))))))
  code := certificateD6_59
  counts := ![(.branch 21 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 32 (.branch 26 (.branch 23 (.leaf (8)) (.leaf (9))) (.branch 29 (.leaf (10)) (.leaf (11)))) (.branch 37 (.branch 34 (.leaf (12)) (.leaf (13))) (.branch 40 (.leaf (14)) (.branch 43 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 24 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 38 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 11 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 25 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.leaf (12)))))),
  (.branch 8 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))) (.branch 28 (.leaf (-3)) (.branch 39 (.leaf (-4)) (.leaf (-5))))),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 19 (.leaf (0)) (.leaf (-25))),
  (.branch 41 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 38 (.branch 35 (.leaf (-7)) (.leaf (-6))) (.branch 41 (.leaf (-5)) (.leaf (-4)))),
  (.branch 39 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 37 (.branch 33 (.branch 31 (.leaf (-14)) (.branch 32 (.leaf (-13)) (.leaf (-12)))) (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.leaf (-8))))) (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 25 (.branch 22 (.branch 20 (.leaf (-25)) (.branch 21 (.leaf (-24)) (.leaf (-23)))) (.branch 23 (.leaf (-22)) (.branch 24 (.leaf (-21)) (.leaf (-20))))) (.branch 28 (.branch 26 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 29 (.leaf (-16)) (.branch 30 (.leaf (-15)) (.leaf (-14)))))) (.branch 37 (.branch 34 (.branch 32 (.leaf (-13)) (.branch 33 (.leaf (-12)) (.leaf (-11)))) (.branch 35 (.leaf (-10)) (.branch 36 (.leaf (-9)) (.leaf (-8))))) (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_003_60 : CycleWitness 6 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (4)) (.branch 7 (.leaf (0)) (.leaf (3)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (5)) (.branch 15 (.leaf (0)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (3)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (4))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.leaf (5)) (.branch 29 (.leaf (0)) (.leaf (3)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (2)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (4)) (.branch 37 (.leaf (0)) (.leaf (1))))) (.branch 41 (.branch 39 (.leaf (2)) (.branch 40 (.leaf (0)) (.leaf (3)))) (.branch 42 (.leaf (1)) (.branch 43 (.leaf (0)) (.leaf (5))))))))
  code := certificateD6_60
  counts := ![(.branch 21 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 32 (.branch 26 (.branch 23 (.leaf (8)) (.leaf (9))) (.branch 29 (.leaf (10)) (.leaf (11)))) (.branch 37 (.branch 34 (.leaf (12)) (.leaf (13))) (.branch 40 (.leaf (14)) (.branch 43 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 24 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 38 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 39 (.leaf (-11)) (.leaf (-12)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 38 (.branch 35 (.leaf (-7)) (.leaf (-6))) (.branch 41 (.leaf (-5)) (.leaf (-4)))),
  (.branch 39 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 41 (.branch 40 (.leaf (-12)) (.leaf (-10))) (.branch 42 (.leaf (-8)) (.branch 43 (.leaf (-6)) (.leaf (-4))))),
  (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-8))) (.branch 39 (.leaf (-7)) (.leaf (-6)))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.leaf (-2))))),
  (.branch 29 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0))))]
def witnessD6_003_61 : CycleWitness 6 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (4)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (5)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (1))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (1)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (5)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (1)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (4)) (.branch 37 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (3)) (.branch 40 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (5)) (.leaf (1))))))))
  code := certificateD6_61
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 11 (.branch 4 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 26 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 40 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 17 (.leaf (-14)) (.leaf (-15)))),
  (.branch 6 (.leaf (0)) (.leaf (-26))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (-2)) (.leaf (-4))))]
  high := ![(.branch 39 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 41 (.leaf (-1)) (.leaf (0))),
  (.branch 42 (.branch 36 (.leaf (-7)) (.leaf (-6))) (.branch 43 (.leaf (-4)) (.leaf (-2)))),
  (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 39 (.branch 22 (.branch 7 (.leaf (-26)) (.leaf (-25))) (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-21)) (.leaf (-18))))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 29 (.leaf (-4)) (.leaf (-3)))]
def witnessD6_003_62 : CycleWitness 6 where
  length := 43
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (1)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (3))))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (1))))) (.branch 29 (.branch 27 (.leaf (5)) (.branch 28 (.leaf (0)) (.leaf (3)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (1)) (.leaf (0)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (4)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (0)) (.leaf (3))))) (.branch 40 (.branch 38 (.leaf (1)) (.branch 39 (.leaf (5)) (.leaf (0)))) (.branch 41 (.leaf (2)) (.branch 42 (.leaf (1)) (.leaf (4))))))))
  code := certificateD6_62
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 36 (.leaf (9)) (.branch 40 (.leaf (10)) (.leaf (11)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 38 (.leaf (9)) (.branch 42 (.leaf (10)) (.leaf (11)))))),
  (.branch 19 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-32)) (.leaf (-39)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 35 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 37 (.leaf (-17)) (.leaf (-19)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 27 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 29 (.branch 21 (.branch 17 (.leaf (-39)) (.leaf (-38))) (.branch 25 (.leaf (-37)) (.leaf (-36)))) (.branch 37 (.branch 33 (.leaf (-35)) (.leaf (-34))) (.branch 41 (.leaf (-33)) (.branch 42 (.leaf (-22)) (.leaf (-11)))))),
  (.leaf (-2)),
  (.branch 36 (.leaf (-7)) (.branch 42 (.leaf (-6)) (.leaf (-4)))),
  (.branch 40 (.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-16)) (.leaf (-13)))) (.branch 41 (.leaf (-10)) (.branch 42 (.leaf (-7)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 40 (.branch 28 (.leaf (-6)) (.leaf (-5))) (.branch 41 (.leaf (-4)) (.branch 42 (.leaf (-3)) (.leaf (-2)))))]
def witnessD6_003_63 : CycleWitness 6 where
  length := 42
  word := (.branch 21 (.branch 11 (.branch 6 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (1))))) (.branch 17 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (0)))) (.branch 18 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (2)))))) (.branch 32 (.branch 27 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (4)) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 38 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 39 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_63
  counts := ![(.branch 20 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (5)) (.leaf (6))))) (.branch 15 (.branch 12 (.branch 10 (.leaf (7)) (.leaf (8))) (.branch 13 (.leaf (9)) (.leaf (10)))) (.branch 17 (.branch 16 (.leaf (11)) (.leaf (12))) (.branch 19 (.leaf (13)) (.leaf (14)))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (15)) (.leaf (16))) (.branch 24 (.leaf (17)) (.leaf (18)))) (.branch 29 (.branch 27 (.leaf (19)) (.leaf (20))) (.branch 30 (.leaf (21)) (.leaf (22))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (23)) (.leaf (24))) (.branch 36 (.leaf (25)) (.leaf (26)))) (.branch 40 (.branch 38 (.leaf (27)) (.leaf (28))) (.branch 41 (.leaf (29)) (.leaf (30))))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 3 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-28))),
  (.branch 28 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 39 (.leaf (-6)) (.leaf (-5))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 21 (.branch 17 (.branch 15 (.leaf (-28)) (.branch 16 (.leaf (-27)) (.leaf (-26)))) (.branch 19 (.branch 18 (.leaf (-25)) (.leaf (-24))) (.branch 20 (.leaf (-23)) (.leaf (-22))))) (.branch 24 (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19)))) (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))))) (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_003_64 : CycleWitness 6 where
  length := 42
  word := (.branch 21 (.branch 11 (.branch 6 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 18 (.leaf (5)) (.branch 20 (.leaf (0)) (.leaf (1)))))) (.branch 32 (.branch 27 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (4))))) (.branch 38 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (0)))) (.branch 39 (.leaf (5)) (.branch 41 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_64
  counts := ![(.branch 20 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (5)) (.leaf (6))))) (.branch 15 (.branch 12 (.branch 10 (.leaf (7)) (.leaf (8))) (.branch 13 (.leaf (9)) (.leaf (10)))) (.branch 17 (.branch 16 (.leaf (11)) (.leaf (12))) (.branch 19 (.leaf (13)) (.leaf (14)))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (15)) (.leaf (16))) (.branch 24 (.leaf (17)) (.leaf (18)))) (.branch 29 (.branch 27 (.leaf (19)) (.leaf (20))) (.branch 30 (.leaf (21)) (.leaf (22))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (23)) (.leaf (24))) (.branch 36 (.leaf (25)) (.leaf (26)))) (.branch 40 (.branch 38 (.leaf (27)) (.leaf (28))) (.branch 41 (.leaf (29)) (.leaf (30))))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 3 (.leaf (-4)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 11 (.leaf (0)) (.leaf (-10))),
  (.branch 18 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 39 (.leaf (-6)) (.leaf (-5))),
  (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 34 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6))))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_003_65 : CycleWitness 6 where
  length := 42
  word := (.branch 22 (.branch 10 (.branch 5 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 8 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 9 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 13 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (0)))) (.branch 19 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (0)))))) (.branch 31 (.branch 25 (.branch 23 (.leaf (1)) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (0)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_65
  counts := ![(.branch 21 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (5)) (.leaf (6))))) (.branch 15 (.branch 12 (.leaf (7)) (.branch 13 (.leaf (8)) (.leaf (9)))) (.branch 18 (.branch 16 (.leaf (10)) (.leaf (11))) (.branch 19 (.leaf (12)) (.leaf (13)))))) (.branch 32 (.branch 26 (.branch 22 (.leaf (14)) (.branch 24 (.leaf (15)) (.leaf (16)))) (.branch 29 (.branch 27 (.leaf (17)) (.leaf (18))) (.branch 30 (.leaf (19)) (.leaf (20))))) (.branch 36 (.branch 33 (.leaf (21)) (.branch 35 (.leaf (22)) (.leaf (23)))) (.branch 40 (.branch 38 (.leaf (24)) (.leaf (25))) (.branch 41 (.leaf (26)) (.leaf (27))))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-10)) (.branch 8 (.leaf (-11)) (.leaf (-12))))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (-2))) (.branch 25 (.leaf (-5)) (.branch 39 (.leaf (-7)) (.leaf (-9))))),
  (.branch 14 (.leaf (0)) (.leaf (-28))),
  (.branch 28 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 37 (.leaf (-12)) (.leaf (-9))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7)))),
  (.branch 28 (.branch 21 (.branch 17 (.branch 15 (.leaf (-28)) (.branch 16 (.leaf (-27)) (.leaf (-26)))) (.branch 19 (.branch 18 (.leaf (-25)) (.leaf (-24))) (.branch 20 (.leaf (-23)) (.leaf (-22))))) (.branch 24 (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19)))) (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))))) (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_003_66 : CycleWitness 6 where
  length := 42
  word := (.branch 21 (.branch 11 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (1))))))) (.branch 32 (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (2)) (.leaf (0))) (.branch 35 (.leaf (1)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (1)) (.leaf (0))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (0)) (.leaf (1))))))))
  code := certificateD6_66
  counts := ![(.branch 20 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 15 (.branch 11 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))) (.branch 16 (.leaf (9)) (.branch 18 (.leaf (10)) (.leaf (11)))))) (.branch 30 (.branch 25 (.branch 22 (.leaf (12)) (.branch 23 (.leaf (13)) (.leaf (14)))) (.branch 27 (.leaf (15)) (.branch 29 (.leaf (16)) (.leaf (17))))) (.branch 36 (.branch 32 (.leaf (18)) (.branch 34 (.leaf (19)) (.leaf (20)))) (.branch 39 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 41 (.leaf (23)) (.leaf (24))))))),
  (.branch 21 (.branch 10 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 38 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-30))),
  (.branch 26 (.leaf (0)) (.leaf (-16))),
  (.branch 40 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 38 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))),
  (.branch 39 (.leaf (-1)) (.leaf (0))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 19 (.branch 15 (.branch 13 (.leaf (-30)) (.branch 14 (.leaf (-29)) (.leaf (-28)))) (.branch 17 (.branch 16 (.leaf (-27)) (.leaf (-26))) (.branch 18 (.leaf (-25)) (.leaf (-24))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-23)) (.leaf (-22))) (.branch 22 (.leaf (-21)) (.leaf (-20)))) (.branch 25 (.branch 24 (.leaf (-19)) (.leaf (-18))) (.branch 26 (.leaf (-17)) (.leaf (-16)))))) (.branch 34 (.branch 30 (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_003_67 : CycleWitness 6 where
  length := 42
  word := (.branch 21 (.branch 11 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (4)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (0))) (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (3))))))) (.branch 32 (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (5)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (0)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (4)) (.leaf (0))) (.branch 35 (.leaf (1)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (0)) (.leaf (3))))))))
  code := certificateD6_67
  counts := ![(.branch 20 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 15 (.branch 11 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))) (.branch 16 (.leaf (9)) (.branch 18 (.leaf (10)) (.leaf (11)))))) (.branch 30 (.branch 25 (.branch 22 (.leaf (12)) (.branch 23 (.leaf (13)) (.leaf (14)))) (.branch 27 (.leaf (15)) (.branch 29 (.leaf (16)) (.leaf (17))))) (.branch 36 (.branch 32 (.leaf (18)) (.branch 34 (.leaf (19)) (.leaf (20)))) (.branch 39 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 41 (.leaf (23)) (.leaf (24))))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 38 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))),
  (.branch 38 (.branch 36 (.branch 25 (.leaf (-15)) (.leaf (-14))) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_003_68 : CycleWitness 6 where
  length := 42
  word := (.branch 21 (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 7 (.leaf (3)) (.leaf (0))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (5)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (3))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (2))))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (3))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (2)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (3)) (.leaf (1))))))))
  code := certificateD6_68
  counts := ![(.branch 19 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 31 (.branch 25 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 28 (.leaf (10)) (.leaf (11)))) (.branch 37 (.branch 34 (.leaf (12)) (.leaf (13))) (.branch 40 (.leaf (14)) (.leaf (15)))))),
  (.branch 24 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 19 (.leaf (-30)) (.leaf (-32)))),
  (.leaf (0)),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 20 (.leaf (-14)) (.branch 32 (.leaf (-20)) (.leaf (-22))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 33 (.leaf (-4)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.branch 35 (.leaf (-20)) (.leaf (-23)))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 29 (.branch 23 (.branch 20 (.leaf (-32)) (.leaf (-31))) (.branch 26 (.leaf (-30)) (.leaf (-29)))) (.branch 35 (.branch 32 (.leaf (-28)) (.leaf (-27))) (.branch 38 (.leaf (-26)) (.branch 41 (.leaf (-25)) (.leaf (-17)))))),
  (.leaf (0)),
  (.branch 40 (.branch 33 (.leaf (-22)) (.leaf (-19))) (.branch 41 (.leaf (-15)) (.leaf (-11)))),
  (.branch 34 (.leaf (-9)) (.leaf (-8))),
  (.branch 38 (.branch 36 (.leaf (-23)) (.branch 37 (.leaf (-20)) (.leaf (-17)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-11))) (.branch 41 (.leaf (-8)) (.leaf (-5))))),
  (.branch 39 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_003_69 : CycleWitness 6 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (0))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (5)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2))))))))
  code := certificateD6_69
  counts := ![(.branch 19 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 21 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 35 (.branch 33 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 40 (.leaf (17)) (.leaf (18))))))),
  (.branch 20 (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 28 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (7)) (.branch 42 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.branch 7 (.leaf (-6)) (.leaf (-7))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 22 (.leaf (-2)) (.branch 36 (.leaf (-3)) (.leaf (-4))))),
  (.branch 11 (.leaf (0)) (.leaf (-31))),
  (.branch 25 (.leaf (0)) (.leaf (-17))),
  (.branch 39 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 36 (.leaf (-7)) (.branch 41 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.leaf (-3)) (.leaf (-2))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.branch 40 (.leaf (-1)) (.leaf (0))))),
  (.branch 26 (.branch 18 (.branch 14 (.branch 12 (.leaf (-31)) (.branch 13 (.leaf (-30)) (.leaf (-29)))) (.branch 16 (.branch 15 (.leaf (-28)) (.leaf (-27))) (.branch 17 (.leaf (-26)) (.leaf (-25))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-24)) (.leaf (-23))) (.branch 21 (.leaf (-22)) (.leaf (-21)))) (.branch 24 (.branch 23 (.leaf (-20)) (.leaf (-19))) (.branch 25 (.leaf (-18)) (.leaf (-17)))))) (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_003_70 : CycleWitness 6 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (5)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (5)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (4))))))))
  code := certificateD6_70
  counts := ![(.branch 20 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 34 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 41 (.leaf (17)) (.leaf (18))))))),
  (.branch 19 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-9))) (.branch 32 (.leaf (-15)) (.leaf (-20)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 18 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 39 (.leaf (-5)) (.leaf (-3))),
  (.branch 41 (.leaf (-4)) (.leaf (-2))),
  (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))),
  (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_003_71 : CycleWitness 6 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (5))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (4)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (5))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (3)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (4))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (5)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (3))))))))
  code := certificateD6_71
  counts := ![(.branch 20 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 34 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 41 (.leaf (17)) (.leaf (18))))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 23 (.leaf (-8)) (.branch 40 (.leaf (-9)) (.leaf (-10))))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-9)) (.leaf (-10)))),
  (.branch 12 (.leaf (0)) (.branch 39 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 39 (.leaf (-5)) (.leaf (-3))),
  (.branch 41 (.leaf (-10)) (.leaf (-7))),
  (.branch 38 (.branch 36 (.leaf (-14)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 32 (.branch 31 (.leaf (-3)) (.leaf (-2))) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 37 (.branch 34 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6))))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_003_72 : CycleWitness 6 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (4)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (3)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (5)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (2))))))))
  code := certificateD6_72
  counts := ![(.branch 20 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 34 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 41 (.leaf (17)) (.leaf (18))))))),
  (.branch 19 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-9))) (.branch 32 (.leaf (-15)) (.leaf (-20)))),
  (.branch 18 (.leaf (0)) (.leaf (-24))),
  (.branch 39 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 39 (.leaf (-5)) (.leaf (-3))),
  (.branch 41 (.leaf (-4)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))),
  (.branch 30 (.branch 24 (.branch 21 (.branch 19 (.leaf (-24)) (.branch 20 (.leaf (-23)) (.leaf (-22)))) (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19))))) (.branch 27 (.branch 25 (.leaf (-18)) (.branch 26 (.leaf (-17)) (.leaf (-16)))) (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))))) (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_003_73 : CycleWitness 6 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (5)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (3)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (3)) (.leaf (2))))))))
  code := certificateD6_73
  counts := ![(.branch 19 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 24 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 34 (.branch 32 (.leaf (12)) (.leaf (13))) (.branch 37 (.leaf (14)) (.branch 40 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-7)) (.branch 26 (.leaf (-9)) (.leaf (-10))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))) (.branch 18 (.leaf (-11)) (.branch 39 (.leaf (-13)) (.leaf (-14))))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-11)) (.leaf (-13)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (-3))) (.branch 38 (.leaf (-5)) (.leaf (-7))))]
  high := ![(.branch 38 (.branch 35 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.leaf (-5)))),
  (.branch 40 (.leaf (-14)) (.branch 41 (.leaf (-10)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 31 (.leaf (-3)) (.leaf (-2))),
  (.branch 37 (.branch 34 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 35 (.leaf (-11)) (.branch 36 (.leaf (-10)) (.leaf (-9))))) (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 40 (.branch 39 (.leaf (-7)) (.leaf (-6))) (.branch 41 (.leaf (-5)) (.leaf (-4))))]
def witnessD6_003_74 : CycleWitness 6 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (1)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (5)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (3))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (0)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (4)) (.leaf (0))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (1)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (3))))))))
  code := certificateD6_74
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 22 (.leaf (-13)) (.leaf (-16)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))) (.branch 18 (.leaf (-11)) (.branch 39 (.leaf (-13)) (.leaf (-14))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 13 (.leaf (-10)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-10)) (.leaf (-11)))),
  (.branch 11 (.leaf (0)) (.branch 38 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 34 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 38 (.leaf (-13)) (.leaf (-11)))),
  (.branch 40 (.leaf (-14)) (.branch 41 (.leaf (-10)) (.leaf (-6)))),
  (.branch 35 (.leaf (-11)) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 36 (.branch 33 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_003_75 : CycleWitness 6 where
  length := 41
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (5))) (.branch 18 (.leaf (3)) (.branch 19 (.leaf (0)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (4)) (.branch 29 (.leaf (1)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (2))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (3))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (5)) (.leaf (2)))) (.branch 39 (.leaf (1)) (.branch 40 (.leaf (0)) (.leaf (3))))))))
  code := certificateD6_75
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 31 (.branch 24 (.branch 22 (.leaf (7)) (.leaf (8))) (.branch 27 (.leaf (9)) (.leaf (10)))) (.branch 36 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 40 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 25 (.leaf (5)) (.leaf (6))) (.branch 34 (.leaf (7)) (.branch 39 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.leaf (7))))),
  (.branch 7 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 29 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-20)) (.leaf (-25)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-27))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 37 (.leaf (-3)) (.leaf (-2))),
  (.branch 35 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-6)))),
  (.branch 27 (.branch 15 (.leaf (-25)) (.branch 21 (.leaf (-24)) (.leaf (-23)))) (.branch 39 (.branch 33 (.leaf (-22)) (.leaf (-21))) (.branch 40 (.leaf (-14)) (.leaf (-7))))),
  (.branch 36 (.leaf (-1)) (.leaf (0))),
  (.branch 34 (.branch 30 (.branch 8 (.leaf (-27)) (.branch 29 (.leaf (-26)) (.leaf (-24)))) (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-20))) (.branch 33 (.leaf (-18)) (.leaf (-16))))) (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-12)) (.leaf (-10)))) (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-6))) (.branch 40 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-6))) (.branch 40 (.leaf (-4)) (.leaf (-2))))]
def witnessD6_003_76 : CycleWitness 6 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 6 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (2))))) (.branch 16 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (4)) (.branch 19 (.leaf (0)) (.leaf (2)))))) (.branch 30 (.branch 26 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (0)))) (.branch 27 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.leaf (5)) (.branch 39 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_76
  counts := ![(.branch 19 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (5)) (.leaf (6))))) (.branch 13 (.branch 11 (.leaf (7)) (.branch 12 (.leaf (8)) (.leaf (9)))) (.branch 16 (.branch 15 (.leaf (10)) (.leaf (11))) (.branch 18 (.leaf (12)) (.leaf (13)))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (14)) (.branch 22 (.leaf (15)) (.leaf (16)))) (.branch 26 (.branch 25 (.leaf (17)) (.leaf (18))) (.branch 28 (.leaf (19)) (.leaf (20))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (21)) (.leaf (22))) (.branch 33 (.leaf (23)) (.leaf (24)))) (.branch 38 (.branch 36 (.leaf (25)) (.leaf (26))) (.branch 39 (.leaf (27)) (.leaf (28))))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 3 (.leaf (-6)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 17 (.leaf (0)) (.leaf (-23))),
  (.branch 37 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 34 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7)))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 22 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_003_77 : CycleWitness 6 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (4)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (3)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (1)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.leaf (5)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (1))))))))
  code := certificateD6_77
  counts := ![(.branch 18 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))))) (.branch 28 (.branch 22 (.branch 21 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.branch 26 (.leaf (13)) (.leaf (14))))) (.branch 34 (.branch 31 (.leaf (15)) (.branch 32 (.leaf (16)) (.leaf (17)))) (.branch 36 (.leaf (18)) (.branch 38 (.leaf (19)) (.leaf (20))))))),
  (.branch 20 (.branch 10 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-25))),
  (.branch 35 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 21 (.branch 18 (.branch 16 (.leaf (-25)) (.branch 17 (.leaf (-24)) (.leaf (-23)))) (.branch 19 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20))))) (.branch 24 (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17)))) (.branch 25 (.leaf (-16)) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_003_78 : CycleWitness 6 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (5)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (3))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (1))))))))
  code := certificateD6_78
  counts := ![(.branch 18 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 22 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 25 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 35 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))) (.branch 22 (.leaf (-11)) (.branch 35 (.leaf (-14)) (.leaf (-15))))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-30))),
  (.branch 30 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 36 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-11)))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 38 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.leaf (-30)) (.branch 12 (.leaf (-29)) (.leaf (-28)))) (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.leaf (-20)))) (.branch 23 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.leaf (-16)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_003 : Fin 23 → CycleWitness 6 := ![witnessD6_003_56, witnessD6_003_57, witnessD6_003_58, witnessD6_003_59, witnessD6_003_60, witnessD6_003_61, witnessD6_003_62, witnessD6_003_63, witnessD6_003_64, witnessD6_003_65, witnessD6_003_66, witnessD6_003_67, witnessD6_003_68, witnessD6_003_69, witnessD6_003_70, witnessD6_003_71, witnessD6_003_72, witnessD6_003_73, witnessD6_003_74, witnessD6_003_75, witnessD6_003_76, witnessD6_003_77, witnessD6_003_78]
end RealPinwheel.FiveSixths


