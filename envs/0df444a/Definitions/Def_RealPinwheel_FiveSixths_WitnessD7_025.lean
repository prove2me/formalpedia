-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_025
-- name    : RealPinwheel_FiveSixths_WitnessD7_025
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:37:20.042045+00:00
-- url     : https://prove2.me/theorems/1d84266c-dcba-463a-b981-a9703946f931
-- title:
--   Exact witness block D7_025
-- statement:
--   These exact witnesses represent words 274 through 289 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 274–289; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_025_273 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (4))) (.branch 10 (.leaf (2)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (3))) (.branch 14 (.leaf (2)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (5)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (6)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (4))) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (3))) (.branch 44 (.leaf (2)) (.leaf (0)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (5)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (3))) (.branch 51 (.leaf (0)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (4))) (.branch 55 (.leaf (0)) (.leaf (6)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_273
  counts := ![(.branch 28 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))) (.branch 45 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 48 (.leaf (14)) (.leaf (15))) (.branch 55 (.leaf (16)) (.branch 58 (.leaf (17)) (.leaf (18))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 23 (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-4)) (.leaf (-5)))) (.branch 44 (.branch 33 (.leaf (-7)) (.leaf (-9))) (.branch 49 (.leaf (-10)) (.branch 53 (.leaf (-11)) (.leaf (-13)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 35 (.leaf (-4)) (.branch 50 (.leaf (-5)) (.leaf (-6))))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 52 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 58 (.branch 57 (.leaf (-10)) (.leaf (-9))) (.branch 59 (.leaf (-8)) (.leaf (-7))))),
  (.branch 51 (.leaf (-6)) (.leaf (-5))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_025_274 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (5))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (6))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (5)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (4))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (3)) (.leaf (6))) (.branch 40 (.leaf (0)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (4)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (6)) (.leaf (3))))))))
  code := certificateD7_274
  counts := ![(.branch 28 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 40 (.leaf (13)) (.leaf (14))))) (.branch 52 (.branch 46 (.leaf (15)) (.branch 49 (.leaf (16)) (.leaf (17)))) (.branch 55 (.leaf (18)) (.branch 58 (.leaf (19)) (.leaf (20))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 39 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 58 (.branch 52 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_025_275 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (1)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (4))) (.branch 21 (.leaf (1)) (.leaf (6))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (4))) (.branch 36 (.leaf (1)) (.leaf (3))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 40 (.leaf (1)) (.leaf (6)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (2))) (.branch 44 (.leaf (1)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (4))) (.branch 51 (.leaf (1)) (.leaf (5))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (1)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_275
  counts := ![(.branch 27 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 34 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 29 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 13 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (-7))) (.branch 45 (.leaf (-12)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.branch 30 (.leaf (-10)) (.leaf (-12)))),
  (.branch 41 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 54 (.branch 50 (.leaf (-14)) (.leaf (-13))) (.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-8)) (.leaf (-4))))),
  (.branch 52 (.branch 48 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.leaf (-4)))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-10)) (.leaf (-8))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 55 (.branch 53 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 54 (.leaf (-10)) (.leaf (-9)))) (.branch 57 (.branch 56 (.leaf (-8)) (.leaf (-7))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 42 (.leaf (-1)) (.leaf (0)))]
def witnessD7_025_276 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (6)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (6))) (.branch 36 (.leaf (0)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (4)) (.leaf (0))) (.branch 40 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (5)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (6))) (.branch 55 (.leaf (0)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (2))) (.branch 59 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_276
  counts := ![(.branch 29 (.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 36 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 33 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 20 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 31 (.leaf (-4)) (.branch 50 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 51 (.leaf (-6)) (.leaf (-5))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-6))) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_025_277 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (1))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (6))) (.branch 14 (.leaf (0)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (5))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (1)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (5))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (4)) (.leaf (2))) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (6))) (.branch 44 (.leaf (0)) (.leaf (4)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (5))) (.branch 51 (.leaf (0)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (6))) (.branch 59 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_277
  counts := ![(.branch 27 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 44 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 47 (.leaf (14)) (.leaf (15))) (.branch 54 (.leaf (16)) (.branch 57 (.leaf (17)) (.leaf (18))))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 56 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 59 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 57 (.branch 43 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3))))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_025_278 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (6)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (3))) (.branch 21 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (6)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (3)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (6)) (.leaf (3))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (0))) (.branch 40 (.leaf (2)) (.leaf (4)))) (.branch 43 (.branch 42 (.leaf (5)) (.leaf (1))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (6)) (.leaf (4))) (.branch 51 (.leaf (2)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (3))) (.branch 55 (.leaf (5)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (1))) (.branch 59 (.leaf (4)) (.leaf (6))))))))
  code := certificateD7_278
  counts := ![(.branch 26 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 44 (.branch 35 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 39 (.leaf (9)) (.leaf (10)))) (.branch 52 (.branch 48 (.leaf (11)) (.leaf (12))) (.branch 56 (.leaf (13)) (.leaf (14)))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-23))) (.branch 9 (.leaf (-25)) (.branch 26 (.leaf (-27)) (.leaf (-28))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-39)) (.leaf (-43)))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (-11))) (.branch 41 (.leaf (-12)) (.leaf (-13)))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 58 (.branch 57 (.leaf (-28)) (.leaf (-21))) (.branch 59 (.leaf (-14)) (.leaf (-7)))),
  (.branch 48 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 56 (.branch 12 (.leaf (-43)) (.branch 55 (.leaf (-42)) (.leaf (-35)))) (.branch 58 (.branch 57 (.leaf (-28)) (.leaf (-21))) (.branch 59 (.leaf (-14)) (.leaf (-7))))),
  (.branch 42 (.leaf (-13)) (.branch 51 (.leaf (-10)) (.leaf (-7)))),
  (.branch 57 (.branch 43 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_025_279 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (6))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (5))) (.branch 21 (.leaf (3)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (6)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (3)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (5))) (.branch 36 (.leaf (0)) (.leaf (3))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (6))) (.branch 40 (.leaf (0)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (1))) (.branch 44 (.leaf (0)) (.leaf (5)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (4)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (3))) (.branch 55 (.leaf (6)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (4)) (.leaf (5))))))))
  code := certificateD7_279
  counts := ![(.branch 27 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 44 (.branch 36 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 40 (.leaf (9)) (.leaf (10)))) (.branch 53 (.branch 49 (.leaf (11)) (.leaf (12))) (.branch 57 (.leaf (13)) (.leaf (14)))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-23))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 18 (.leaf (-8)) (.leaf (-9)))),
  (.branch 37 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 54 (.leaf (-19)) (.leaf (-20)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 35 (.leaf (-7)) (.branch 50 (.leaf (-10)) (.leaf (-13))))),
  (.branch 9 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 45 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-14)) (.leaf (-7))))),
  (.branch 53 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 57 (.branch 55 (.leaf (-20)) (.branch 56 (.leaf (-17)) (.leaf (-14)))) (.branch 58 (.leaf (-11)) (.branch 59 (.leaf (-8)) (.leaf (-5))))),
  (.branch 25 (.leaf (-6)) (.leaf (-5))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-13)) (.leaf (-12))) (.branch 53 (.leaf (-11)) (.branch 54 (.leaf (-10)) (.leaf (-9))))) (.branch 57 (.branch 56 (.leaf (-8)) (.leaf (-7))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 57 (.branch 40 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_025_280 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (4)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (6)) (.leaf (5))) (.branch 21 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (1))) (.branch 25 (.leaf (3)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (1)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (1)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (2))) (.branch 44 (.leaf (4)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (6)) (.leaf (5))) (.branch 51 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (2))) (.branch 55 (.leaf (3)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (5))) (.branch 59 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_280
  counts := ![(.branch 27 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 51 (.leaf (9)) (.branch 56 (.leaf (10)) (.leaf (11)))))),
  (.branch 32 (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 54 (.leaf (9)) (.branch 59 (.leaf (10)) (.leaf (11)))))),
  (.branch 25 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-38))) (.branch 45 (.leaf (-43)) (.leaf (-45)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 15 (.leaf (-10)) (.leaf (-15)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (-14))) (.branch 47 (.leaf (-18)) (.leaf (-20)))),
  (.branch 14 (.leaf (0)) (.branch 44 (.leaf (-2)) (.leaf (-4)))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (-3))) (.branch 58 (.leaf (-7)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 58 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 46 (.leaf (-45)) (.leaf (-44))) (.branch 58 (.leaf (-33)) (.branch 59 (.leaf (-22)) (.leaf (-11))))),
  (.branch 27 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 38 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11))))),
  (.branch 57 (.branch 48 (.leaf (-20)) (.branch 56 (.leaf (-19)) (.leaf (-16)))) (.branch 58 (.leaf (-13)) (.branch 59 (.leaf (-10)) (.leaf (-7))))),
  (.branch 54 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.branch 56 (.leaf (-1)) (.leaf (0))))),
  (.branch 59 (.leaf (-10)) (.leaf (-8))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_025_281 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (4))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (1))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (4))) (.branch 14 (.leaf (6)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (4))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (3)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (1)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (4))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (5)) (.leaf (2))) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (4))) (.branch 44 (.leaf (6)) (.leaf (5)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (4))) (.branch 51 (.leaf (0)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (3)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (4))) (.branch 59 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_281
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 56 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 59 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 58 (.branch 52 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 43 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3))))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 51 (.leaf (-5)) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_025_282 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (5))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (6)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (5)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (6))) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (1))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (5)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_282
  counts := ![(.branch 27 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))) (.branch 44 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 48 (.leaf (14)) (.leaf (15))) (.branch 55 (.leaf (16)) (.branch 57 (.leaf (17)) (.leaf (18))))))),
  (.branch 28 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-12)) (.leaf (-14)))) (.branch 37 (.branch 27 (.leaf (-16)) (.leaf (-18))) (.branch 57 (.leaf (-19)) (.leaf (-21))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 20 (.leaf (-11)) (.branch 50 (.leaf (-14)) (.leaf (-16))))),
  (.branch 22 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-16)) (.leaf (-11)))),
  (.branch 55 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 59 (.leaf (-14)) (.leaf (-9)))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 57 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 54 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_025_283 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (6))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (1))) (.branch 29 (.leaf (4)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (6)))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (0))) (.branch 36 (.leaf (2)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (4)) (.leaf (0))) (.branch 40 (.leaf (2)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (3)) (.leaf (5))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (6)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_283
  counts := ![(.branch 26 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 44 (.branch 35 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 39 (.leaf (9)) (.leaf (10)))) (.branch 52 (.branch 47 (.leaf (11)) (.leaf (12))) (.branch 56 (.leaf (13)) (.leaf (14)))))),
  (.branch 28 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 46 (.branch 37 (.branch 32 (.leaf (7)) (.leaf (8))) (.branch 41 (.leaf (9)) (.leaf (10)))) (.branch 54 (.branch 50 (.leaf (11)) (.leaf (12))) (.branch 58 (.leaf (13)) (.leaf (14)))))),
  (.branch 30 (.branch 15 (.branch 6 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 36 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))) (.branch 17 (.leaf (-12)) (.branch 47 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.branch 32 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 57 (.branch 48 (.leaf (-15)) (.leaf (-14))) (.branch 58 (.leaf (-11)) (.branch 59 (.leaf (-8)) (.leaf (-5))))),
  (.branch 59 (.leaf (-8)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 58 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 49 (.leaf (-2)) (.leaf (-1))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_025_284 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (5))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (6)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (0))) (.branch 29 (.leaf (5)) (.leaf (1))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (6))) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (0))) (.branch 44 (.leaf (3)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (5)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (3))) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (4)) (.leaf (0))) (.branch 59 (.leaf (6)) (.leaf (1))))))))
  code := certificateD7_284
  counts := ![(.branch 28 (.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 23 (.leaf (9)) (.branch 26 (.leaf (10)) (.leaf (11)))))) (.branch 43 (.branch 36 (.branch 31 (.leaf (12)) (.branch 33 (.leaf (13)) (.leaf (14)))) (.branch 38 (.leaf (15)) (.branch 41 (.leaf (16)) (.leaf (17))))) (.branch 51 (.branch 46 (.leaf (18)) (.branch 48 (.leaf (19)) (.leaf (20)))) (.branch 56 (.branch 53 (.leaf (21)) (.leaf (22))) (.branch 58 (.leaf (23)) (.leaf (24))))))),
  (.branch 30 (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 22 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-11)))) (.branch 37 (.leaf (-14)) (.branch 52 (.leaf (-17)) (.leaf (-20))))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 59 (.leaf (-4)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-20)) (.leaf (-19))) (.branch 55 (.leaf (-18)) (.leaf (-17)))) (.branch 58 (.branch 57 (.leaf (-16)) (.leaf (-15))) (.branch 59 (.leaf (-14)) (.leaf (-13))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_025_285 : CycleWitness 7 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (4))) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (5))) (.branch 24 (.leaf (3)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (6)) (.leaf (0))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (4)) (.branch 31 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (3))) (.branch 35 (.leaf (5)) (.leaf (1))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (4)) (.leaf (6)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (3)) (.leaf (2)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (5)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (4))) (.branch 50 (.leaf (2)) (.leaf (1))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (3))) (.branch 54 (.leaf (6)) (.leaf (2)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (4)) (.leaf (5))))))))
  code := certificateD7_285
  counts := ![(.branch 29 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.leaf (15)))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 48 (.leaf (-44)) (.leaf (-47)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 55 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 43 (.leaf (-35)) (.leaf (-37)))),
  (.branch 19 (.leaf (0)) (.branch 58 (.leaf (-1)) (.leaf (-2)))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (-7))) (.branch 28 (.leaf (-8)) (.branch 40 (.leaf (-11)) (.leaf (-12)))))]
  high := ![(.branch 53 (.branch 49 (.leaf (-47)) (.leaf (-46))) (.branch 57 (.leaf (-45)) (.branch 58 (.leaf (-30)) (.leaf (-15))))),
  (.branch 52 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2)))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.leaf (-2)))),
  (.branch 55 (.branch 44 (.leaf (-37)) (.branch 54 (.leaf (-36)) (.leaf (-30)))) (.branch 57 (.branch 56 (.leaf (-24)) (.leaf (-18))) (.branch 58 (.leaf (-12)) (.leaf (-6))))),
  (.leaf (-2)),
  (.branch 24 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 36 (.leaf (-2)) (.branch 48 (.leaf (-1)) (.leaf (0))))),
  (.branch 56 (.branch 41 (.leaf (-12)) (.branch 55 (.leaf (-11)) (.leaf (-10)))) (.branch 57 (.leaf (-9)) (.branch 58 (.leaf (-8)) (.leaf (-7)))))]
def witnessD7_025_286 : CycleWitness 7 where
  length := 59
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (5))) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (4)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (6))) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (1))) (.branch 24 (.leaf (5)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (4))) (.branch 28 (.leaf (2)) (.leaf (0))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.leaf (3)) (.branch 31 (.leaf (1)) (.leaf (6)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (5))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (3)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (2))) (.branch 43 (.leaf (1)) (.leaf (6)))))) (.branch 51 (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (5)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (2)) (.leaf (0))) (.branch 50 (.leaf (3)) (.leaf (4))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (1)) (.leaf (0))) (.branch 54 (.leaf (6)) (.leaf (2)))) (.branch 57 (.branch 56 (.leaf (1)) (.leaf (0))) (.branch 58 (.leaf (5)) (.leaf (3))))))))
  code := certificateD7_286
  counts := ![(.branch 29 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.leaf (15)))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 38 (.leaf (9)) (.leaf (10)))) (.branch 52 (.branch 47 (.leaf (11)) (.leaf (12))) (.branch 56 (.leaf (13)) (.leaf (14)))))),
  (.branch 28 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-44))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 14 (.leaf (-20)) (.leaf (-26)))) (.branch 34 (.branch 26 (.leaf (-29)) (.leaf (-35))) (.branch 38 (.leaf (-41)) (.leaf (-44))))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-29)) (.leaf (-42)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-39)) (.leaf (-42)))),
  (.branch 46 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.branch 54 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 30 (.branch 14 (.branch 6 (.branch 2 (.leaf (-44)) (.leaf (-43))) (.branch 10 (.leaf (-42)) (.leaf (-41)))) (.branch 22 (.branch 18 (.leaf (-40)) (.leaf (-39))) (.branch 26 (.leaf (-38)) (.leaf (-37))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (-36)) (.leaf (-35))) (.branch 42 (.leaf (-34)) (.leaf (-33)))) (.branch 54 (.branch 50 (.leaf (-32)) (.leaf (-31))) (.branch 58 (.leaf (-30)) (.leaf (-15)))))),
  (.branch 48 (.branch 39 (.leaf (-44)) (.leaf (-43))) (.branch 57 (.leaf (-42)) (.branch 58 (.leaf (-35)) (.leaf (-28))))),
  (.branch 49 (.branch 9 (.leaf (-42)) (.branch 29 (.leaf (-41)) (.leaf (-40)))) (.branch 57 (.branch 56 (.leaf (-37)) (.leaf (-29))) (.branch 58 (.leaf (-21)) (.leaf (-13))))),
  (.leaf (0)),
  (.branch 54 (.branch 40 (.branch 28 (.leaf (-42)) (.leaf (-41))) (.branch 52 (.leaf (-40)) (.branch 53 (.leaf (-35)) (.leaf (-30))))) (.branch 56 (.branch 55 (.leaf (-25)) (.leaf (-20))) (.branch 57 (.leaf (-15)) (.branch 58 (.leaf (-10)) (.leaf (-5)))))),
  (.leaf (-2)),
  (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (-2)))))]
def witnessD7_025_287 : CycleWitness 7 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (4)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (6))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (4)) (.leaf (5))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (3))) (.branch 35 (.leaf (0)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (6)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (4)) (.leaf (0)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (3)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (5))) (.branch 49 (.leaf (0)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (0)) (.leaf (3))) (.branch 53 (.leaf (0)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (4)) (.leaf (6))))))))
  code := certificateD7_287
  counts := ![(.branch 27 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))) (.branch 43 (.branch 35 (.branch 30 (.leaf (11)) (.branch 32 (.leaf (12)) (.leaf (13)))) (.branch 37 (.leaf (14)) (.branch 40 (.leaf (15)) (.leaf (16))))) (.branch 51 (.branch 46 (.leaf (17)) (.branch 49 (.leaf (18)) (.leaf (19)))) (.branch 53 (.leaf (20)) (.branch 56 (.leaf (21)) (.leaf (22))))))),
  (.branch 26 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 24 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 8 (.leaf (-10)) (.leaf (-12)))) (.branch 37 (.branch 32 (.leaf (-14)) (.leaf (-15))) (.branch 53 (.leaf (-17)) (.leaf (-19))))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-20)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 39 (.leaf (-14)) (.leaf (-15)))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 52 (.leaf (-7)) (.leaf (-8)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-31))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 54 (.leaf (-19)) (.branch 57 (.leaf (-18)) (.leaf (-14)))),
  (.branch 51 (.branch 46 (.leaf (-20)) (.leaf (-19))) (.branch 56 (.leaf (-18)) (.branch 57 (.leaf (-12)) (.leaf (-6))))),
  (.branch 55 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-8)) (.leaf (-5))))),
  (.branch 55 (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3))))),
  (.branch 43 (.leaf (-3)) (.leaf (-2))),
  (.branch 52 (.branch 49 (.branch 10 (.leaf (-31)) (.leaf (-30))) (.branch 50 (.leaf (-27)) (.branch 51 (.leaf (-24)) (.leaf (-21))))) (.branch 55 (.branch 53 (.leaf (-18)) (.branch 54 (.leaf (-15)) (.leaf (-12)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 39 (.leaf (-2)) (.leaf (0)))]
def witnessD7_025_288 : CycleWitness 7 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (4)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (2)) (.leaf (5))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (3))) (.branch 35 (.leaf (0)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (6)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (3)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (5)) (.leaf (1))) (.branch 49 (.leaf (3)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (4)) (.leaf (2))) (.branch 53 (.leaf (0)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (3))) (.branch 57 (.leaf (2)) (.leaf (6))))))))
  code := certificateD7_288
  counts := ![(.branch 26 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 46 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 55 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 33 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 17 (.leaf (-3)) (.branch 46 (.leaf (-4)) (.leaf (-5))))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.branch 33 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (-10))) (.branch 47 (.leaf (-11)) (.leaf (-13)))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 55 (.branch 49 (.leaf (-21)) (.leaf (-20))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-3)),
  (.branch 35 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-4)))),
  (.branch 54 (.branch 52 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 53 (.leaf (-12)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.branch 52 (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 55 (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 19 (.leaf (-2)) (.branch 40 (.leaf (-1)) (.leaf (0))))]
def witnessD7_025 : Fin 16 → CycleWitness 7 := ![witnessD7_025_273, witnessD7_025_274, witnessD7_025_275, witnessD7_025_276, witnessD7_025_277, witnessD7_025_278, witnessD7_025_279, witnessD7_025_280, witnessD7_025_281, witnessD7_025_282, witnessD7_025_283, witnessD7_025_284, witnessD7_025_285, witnessD7_025_286, witnessD7_025_287, witnessD7_025_288]
end RealPinwheel.FiveSixths


