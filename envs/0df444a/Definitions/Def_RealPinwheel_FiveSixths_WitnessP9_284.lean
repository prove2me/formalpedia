-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_284
-- name    : RealPinwheel_FiveSixths_WitnessP9_284
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:14:59.852353+00:00
-- url     : https://prove2.me/theorems/d907e16b-c85f-4d63-976f-bc48be68ca7b
-- title:
--   Exact witness block P9_284
-- statement:
--   These exact witnesses represent words 4677 through 4719 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 4677–4719; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_284_4676 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (6)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (7)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (5))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (8))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (1)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (6)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (4)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (0))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (7)) (.leaf (5)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (6)) (.leaf (0))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (2)) (.leaf (1))) (.branch 46 (.leaf (8)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (4)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 51 (.leaf (0)) (.leaf (5))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (7))) (.branch 59 (.leaf (0)) (.branch 60 (.leaf (2)) (.leaf (1)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (6)) (.leaf (0))) (.branch 64 (.leaf (1)) (.leaf (4)))) (.branch 67 (.branch 66 (.leaf (2)) (.leaf (0))) (.branch 68 (.leaf (1)) (.branch 69 (.leaf (8)) (.leaf (5)))))))))
  code := certificateP9_4676
  counts := ![(.branch 32 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 51 (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.branch 47 (.leaf (12)) (.leaf (13))))) (.branch 59 (.branch 55 (.leaf (14)) (.leaf (15))) (.branch 63 (.leaf (16)) (.branch 67 (.leaf (17)) (.leaf (18))))))),
  (.branch 33 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))) (.branch 53 (.branch 41 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 45 (.leaf (11)) (.branch 49 (.leaf (12)) (.leaf (13))))) (.branch 61 (.branch 56 (.leaf (14)) (.leaf (15))) (.branch 64 (.leaf (16)) (.branch 68 (.leaf (17)) (.leaf (18))))))),
  (.branch 31 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4))))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.branch 70 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 34 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 46 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 69 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-26)) (.leaf (-33)))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 56 (.leaf (-3)) (.leaf (-4)))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 54 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-27))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (-9)) (.leaf (-10)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.branch 42 (.leaf (-12)) (.leaf (-15)))),
  (.branch 11 (.leaf (0)) (.branch 34 (.leaf (-37)) (.leaf (-38)))),
  (.branch 46 (.branch 23 (.leaf (0)) (.leaf (-1))) (.branch 69 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 56 (.branch 48 (.branch 44 (.leaf (-33)) (.leaf (-32))) (.branch 52 (.leaf (-31)) (.leaf (-30)))) (.branch 64 (.branch 60 (.leaf (-29)) (.leaf (-28))) (.branch 68 (.leaf (-27)) (.branch 69 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 69 (.leaf (-4)) (.leaf (-3))),
  (.branch 68 (.branch 67 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3)))),
  (.branch 63 (.branch 59 (.branch 40 (.leaf (-27)) (.branch 58 (.leaf (-26)) (.leaf (-24)))) (.branch 61 (.branch 60 (.leaf (-22)) (.leaf (-20))) (.branch 62 (.leaf (-18)) (.leaf (-16))))) (.branch 66 (.branch 64 (.leaf (-14)) (.branch 65 (.leaf (-12)) (.leaf (-10)))) (.branch 68 (.branch 67 (.leaf (-8)) (.leaf (-6))) (.branch 69 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 67 (.branch 66 (.leaf (-10)) (.leaf (-8))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2))))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 65 (.branch 63 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 64 (.leaf (-13)) (.leaf (-12)))) (.branch 67 (.branch 66 (.leaf (-11)) (.leaf (-10))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-8)) (.leaf (-7)))))),
  (.branch 63 (.branch 60 (.branch 35 (.leaf (-38)) (.branch 59 (.leaf (-36)) (.leaf (-33)))) (.branch 61 (.leaf (-30)) (.branch 62 (.leaf (-27)) (.leaf (-24))))) (.branch 66 (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-18)) (.leaf (-15)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-9))) (.branch 69 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (-3))]
def witnessP9_284_4677 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (5)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (0))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (8)) (.leaf (2))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (7)) (.leaf (3)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (6)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (0))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (8)) (.leaf (5)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (4))) (.branch 42 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (1)) (.leaf (0))) (.branch 46 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 48 (.leaf (5)) (.leaf (0))) (.branch 50 (.leaf (1)) (.branch 51 (.leaf (8)) (.leaf (2))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (6)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (2)) (.branch 60 (.leaf (7)) (.leaf (3)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (5)) (.leaf (0))) (.branch 64 (.leaf (4)) (.leaf (1)))) (.branch 67 (.branch 66 (.leaf (2)) (.leaf (0))) (.branch 68 (.leaf (3)) (.branch 69 (.leaf (8)) (.leaf (6)))))))))
  code := certificateP9_4677
  counts := ![(.branch 32 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 49 (.branch 40 (.branch 36 (.leaf (8)) (.leaf (9))) (.branch 45 (.leaf (10)) (.leaf (11)))) (.branch 58 (.branch 54 (.leaf (12)) (.leaf (13))) (.branch 63 (.leaf (14)) (.branch 67 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 65 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 38 (.leaf (5)) (.branch 46 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 55 (.branch 39 (.leaf (5)) (.branch 47 (.leaf (6)) (.leaf (7)))) (.branch 61 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 62 (.leaf (4)) (.leaf (5))))),
  (.branch 42 (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 56 (.leaf (3)) (.branch 70 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.branch 69 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 40 (.leaf (-19)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 33 (.branch 4 (.leaf (0)) (.branch 26 (.leaf (-7)) (.leaf (-8)))) (.branch 61 (.branch 39 (.leaf (-9)) (.leaf (-12))) (.branch 68 (.leaf (-13)) (.leaf (-14))))),
  (.branch 6 (.leaf (0)) (.branch 29 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.branch 48 (.leaf (-7)) (.leaf (-8)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-19)) (.leaf (-20)))),
  (.branch 16 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 59 (.branch 41 (.leaf (-20)) (.branch 50 (.leaf (-19)) (.leaf (-18)))) (.branch 68 (.leaf (-17)) (.branch 69 (.leaf (-12)) (.leaf (-7))))),
  (.branch 67 (.branch 58 (.leaf (-6)) (.branch 66 (.leaf (-5)) (.leaf (-4)))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1)))),
  (.branch 69 (.leaf (-14)) (.leaf (-12))),
  (.branch 67 (.branch 65 (.leaf (-18)) (.branch 66 (.leaf (-15)) (.leaf (-12)))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3))))),
  (.branch 66 (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.branch 65 (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-18))) (.branch 63 (.leaf (-16)) (.branch 64 (.leaf (-14)) (.leaf (-12))))) (.branch 67 (.branch 66 (.leaf (-10)) (.leaf (-8))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 52 (.leaf (-3)) (.leaf (-2)))]
def witnessP9_284_4678 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (7))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (2))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (8)) (.leaf (2))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (1)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (6))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (1)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (4)) (.leaf (7))) (.branch 29 (.leaf (0)) (.leaf (3)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (5)) (.leaf (4)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (8))) (.branch 42 (.leaf (0)) (.leaf (1))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (4)) (.leaf (2))) (.branch 46 (.leaf (6)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (3)) (.leaf (1))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (7)) (.leaf (2))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (4))) (.branch 55 (.leaf (1)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (5))) (.branch 59 (.leaf (2)) (.branch 60 (.leaf (0)) (.leaf (1)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (4)) (.leaf (8))) (.branch 64 (.leaf (0)) (.leaf (3)))) (.branch 67 (.branch 66 (.leaf (2)) (.leaf (1))) (.branch 68 (.leaf (0)) (.branch 69 (.leaf (6)) (.leaf (4)))))))))
  code := certificateP9_4678
  counts := ![(.branch 33 (.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))) (.branch 50 (.branch 40 (.branch 36 (.leaf (10)) (.leaf (11))) (.branch 42 (.leaf (12)) (.branch 47 (.leaf (13)) (.leaf (14))))) (.branch 60 (.branch 53 (.leaf (15)) (.branch 57 (.leaf (16)) (.leaf (17)))) (.branch 64 (.leaf (18)) (.branch 68 (.leaf (19)) (.leaf (20))))))),
  (.branch 32 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 61 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 67 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 38 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.branch 70 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 46 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 69 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 18 (.leaf (-5)) (.leaf (-6)))) (.branch 42 (.branch 36 (.leaf (-7)) (.leaf (-8))) (.branch 53 (.leaf (-10)) (.branch 60 (.leaf (-11)) (.leaf (-12)))))),
  (.branch 2 (.leaf (0)) (.leaf (-23))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-19)) (.leaf (-21)))),
  (.branch 35 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.branch 34 (.leaf (-37)) (.leaf (-38)))),
  (.branch 46 (.branch 23 (.leaf (0)) (.leaf (-1))) (.branch 69 (.leaf (-2)) (.leaf (-3)))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (-18))) (.branch 51 (.leaf (-20)) (.leaf (-21)))),
  (.branch 16 (.leaf (0)) (.branch 63 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 69 (.leaf (-12)) (.leaf (-11))),
  (.branch 56 (.branch 44 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 50 (.leaf (-21)) (.leaf (-20)))) (.branch 68 (.branch 62 (.leaf (-19)) (.leaf (-18))) (.branch 69 (.leaf (-12)) (.leaf (-6))))),
  (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1)))),
  (.branch 67 (.branch 57 (.leaf (-21)) (.branch 66 (.leaf (-20)) (.leaf (-16)))) (.branch 68 (.leaf (-12)) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 63 (.leaf (-1)) (.leaf (0))),
  (.branch 63 (.branch 60 (.branch 35 (.leaf (-38)) (.branch 59 (.leaf (-36)) (.leaf (-33)))) (.branch 61 (.leaf (-30)) (.branch 62 (.leaf (-27)) (.leaf (-24))))) (.branch 66 (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-18)) (.leaf (-15)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-9))) (.branch 69 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (-3)),
  (.branch 60 (.branch 55 (.branch 53 (.branch 52 (.leaf (-21)) (.leaf (-20))) (.branch 54 (.leaf (-19)) (.leaf (-18)))) (.branch 57 (.branch 56 (.leaf (-17)) (.leaf (-16))) (.branch 58 (.leaf (-15)) (.branch 59 (.leaf (-14)) (.leaf (-13)))))) (.branch 65 (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-11))) (.branch 63 (.leaf (-10)) (.branch 64 (.leaf (-9)) (.leaf (-8))))) (.branch 67 (.branch 66 (.leaf (-7)) (.leaf (-6))) (.branch 68 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-3))))))),
  (.branch 66 (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7)))) (.branch 68 (.branch 67 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3)))))]
def witnessP9_284_4679 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (6))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (8))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (2)) (.leaf (0)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (4))) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (5))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (3)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (6))) (.branch 38 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (7)) (.leaf (0))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (1)) (.leaf (2))) (.branch 46 (.leaf (8)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (3))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (4)) (.leaf (1))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (5)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.branch 60 (.leaf (6)) (.leaf (0)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (1)) (.leaf (3))) (.branch 64 (.leaf (0)) (.leaf (7)))) (.branch 67 (.branch 66 (.leaf (1)) (.leaf (2))) (.branch 68 (.leaf (0)) (.branch 69 (.leaf (1)) (.leaf (8)))))))))
  code := certificateP9_4679
  counts := ![(.branch 33 (.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))) (.branch 50 (.branch 40 (.branch 36 (.leaf (10)) (.leaf (11))) (.branch 43 (.leaf (12)) (.branch 47 (.leaf (13)) (.leaf (14))))) (.branch 61 (.branch 54 (.leaf (15)) (.branch 57 (.leaf (16)) (.leaf (17)))) (.branch 64 (.leaf (18)) (.branch 68 (.leaf (19)) (.leaf (20))))))),
  (.branch 34 (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))) (.branch 52 (.branch 41 (.branch 38 (.leaf (10)) (.leaf (11))) (.branch 44 (.leaf (12)) (.branch 48 (.leaf (13)) (.leaf (14))))) (.branch 62 (.branch 55 (.leaf (15)) (.branch 58 (.leaf (16)) (.leaf (17)))) (.branch 66 (.leaf (18)) (.branch 69 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 39 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 67 (.leaf (9)) (.leaf (10)))))),
  (.branch 35 (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (2)) (.leaf (3)))),
  (.branch 46 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 70 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-58))),
  (.branch 9 (.leaf (0)) (.branch 32 (.leaf (-43)) (.leaf (-44)))),
  (.branch 37 (.branch 14 (.leaf (0)) (.leaf (-28))) (.branch 60 (.leaf (-29)) (.leaf (-30)))),
  (.branch 18 (.leaf (0)) (.leaf (-16))),
  (.branch 23 (.leaf (0)) (.branch 46 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 65 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-2)))),
  (.branch 59 (.leaf (-3)) (.leaf (-2))),
  (.branch 68 (.branch 60 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1)))),
  (.branch 66 (.branch 64 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 55 (.branch 52 (.branch 5 (.leaf (-58)) (.leaf (-57))) (.branch 53 (.leaf (-54)) (.branch 54 (.leaf (-51)) (.leaf (-48))))) (.branch 57 (.branch 56 (.leaf (-45)) (.leaf (-42))) (.branch 58 (.leaf (-39)) (.branch 59 (.leaf (-36)) (.leaf (-33)))))) (.branch 65 (.branch 62 (.branch 61 (.leaf (-30)) (.leaf (-27))) (.branch 63 (.leaf (-24)) (.branch 64 (.leaf (-21)) (.leaf (-18))))) (.branch 67 (.branch 66 (.leaf (-15)) (.leaf (-12))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 62 (.branch 58 (.branch 33 (.leaf (-44)) (.branch 57 (.leaf (-42)) (.leaf (-39)))) (.branch 60 (.branch 59 (.leaf (-36)) (.leaf (-33))) (.branch 61 (.leaf (-30)) (.leaf (-27))))) (.branch 66 (.branch 64 (.branch 63 (.leaf (-24)) (.leaf (-21))) (.branch 65 (.leaf (-18)) (.leaf (-15)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-9))) (.branch 69 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 65 (.branch 62 (.branch 61 (.leaf (-30)) (.leaf (-27))) (.branch 63 (.leaf (-24)) (.branch 64 (.leaf (-21)) (.leaf (-18))))) (.branch 67 (.branch 66 (.leaf (-15)) (.leaf (-12))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 67 (.branch 19 (.leaf (-16)) (.branch 66 (.leaf (-15)) (.leaf (-12)))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3))))),
  (.branch 47 (.leaf (-2)) (.leaf (0)))]
def witnessP9_284_4680 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (3))) (.branch 11 (.leaf (6)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (7))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (8)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (5)) (.leaf (0)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (6))) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (7))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (8)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (3)) (.leaf (4)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (5)) (.leaf (0))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (1)) (.leaf (2))) (.branch 46 (.leaf (6)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (7))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (3))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (8)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (4)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.branch 60 (.leaf (5)) (.leaf (0)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (1)) (.leaf (6))) (.branch 64 (.leaf (0)) (.leaf (1)))) (.branch 67 (.branch 66 (.leaf (3)) (.leaf (7))) (.branch 68 (.leaf (0)) (.branch 69 (.leaf (1)) (.leaf (8)))))))))
  code := certificateP9_4680
  counts := ![(.branch 33 (.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))) (.branch 50 (.branch 40 (.branch 36 (.leaf (10)) (.leaf (11))) (.branch 43 (.leaf (12)) (.branch 47 (.leaf (13)) (.leaf (14))))) (.branch 61 (.branch 54 (.leaf (15)) (.branch 57 (.leaf (16)) (.leaf (17)))) (.branch 64 (.leaf (18)) (.branch 68 (.leaf (19)) (.leaf (20))))))),
  (.branch 34 (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))) (.branch 51 (.branch 41 (.branch 37 (.leaf (10)) (.leaf (11))) (.branch 44 (.leaf (12)) (.branch 48 (.leaf (13)) (.leaf (14))))) (.branch 62 (.branch 55 (.leaf (15)) (.branch 58 (.leaf (16)) (.leaf (17)))) (.branch 65 (.leaf (18)) (.branch 69 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 66 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 67 (.leaf (3)) (.leaf (4))))),
  (.branch 35 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.branch 70 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-27)) (.leaf (-28)))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (-13)) (.leaf (-14)))),
  (.branch 14 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 65 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-2)))),
  (.branch 66 (.leaf (-3)) (.leaf (-2))),
  (.branch 64 (.branch 61 (.branch 60 (.leaf (-11)) (.leaf (-10))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-8)) (.leaf (-7))))) (.branch 67 (.branch 65 (.leaf (-6)) (.branch 66 (.leaf (-5)) (.leaf (-4)))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1)))),
  (.branch 63 (.branch 59 (.branch 57 (.leaf (-28)) (.branch 58 (.leaf (-26)) (.leaf (-24)))) (.branch 61 (.branch 60 (.leaf (-22)) (.leaf (-20))) (.branch 62 (.leaf (-18)) (.leaf (-16))))) (.branch 66 (.branch 64 (.leaf (-14)) (.branch 65 (.leaf (-12)) (.leaf (-10)))) (.branch 68 (.branch 67 (.leaf (-8)) (.leaf (-6))) (.branch 69 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 64 (.branch 61 (.branch 43 (.leaf (-21)) (.leaf (-20))) (.branch 62 (.leaf (-18)) (.branch 63 (.leaf (-16)) (.leaf (-14))))) (.branch 67 (.branch 65 (.leaf (-12)) (.branch 66 (.leaf (-10)) (.leaf (-8)))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 66 (.branch 64 (.leaf (-14)) (.branch 65 (.leaf (-12)) (.leaf (-10)))) (.branch 68 (.branch 67 (.leaf (-8)) (.leaf (-6))) (.branch 69 (.leaf (-4)) (.leaf (-2))))),
  (.branch 68 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 69 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0))]
def witnessP9_284_4681 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (6)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (8)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (1))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (5))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (7))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (6)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (4)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (8)) (.branch 34 (.leaf (2)) (.leaf (5)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (3)) (.leaf (4)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (2))) (.branch 42 (.leaf (6)) (.leaf (1))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (3))) (.branch 46 (.leaf (7)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (4)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 51 (.leaf (0)) (.leaf (5))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (4)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (8))) (.branch 59 (.leaf (0)) (.branch 60 (.leaf (1)) (.leaf (3)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (6)) (.leaf (0))) (.branch 64 (.leaf (2)) (.leaf (4)))) (.branch 67 (.branch 66 (.leaf (1)) (.leaf (0))) (.branch 68 (.leaf (7)) (.branch 69 (.leaf (3)) (.leaf (5)))))))))
  code := certificateP9_4681
  counts := ![(.branch 32 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 51 (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.branch 47 (.leaf (12)) (.leaf (13))))) (.branch 59 (.branch 55 (.leaf (14)) (.leaf (15))) (.branch 63 (.leaf (16)) (.branch 67 (.leaf (17)) (.leaf (18))))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 41 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 38 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 45 (.leaf (5)) (.leaf (6))) (.branch 61 (.leaf (7)) (.branch 69 (.leaf (8)) (.leaf (9)))))),
  (.branch 30 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.branch 70 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 46 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 68 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-26)) (.leaf (-32)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-23)) (.leaf (-26)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 41 (.leaf (-6)) (.branch 64 (.leaf (-7)) (.leaf (-8))))),
  (.branch 6 (.leaf (0)) (.branch 29 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-19)) (.leaf (-21)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.branch 42 (.leaf (-12)) (.leaf (-15)))),
  (.branch 46 (.branch 23 (.leaf (0)) (.leaf (-1))) (.branch 68 (.leaf (-2)) (.leaf (-4)))),
  (.branch 11 (.leaf (0)) (.branch 33 (.leaf (-13)) (.leaf (-15))))]
  high := ![(.branch 60 (.branch 52 (.branch 48 (.leaf (-32)) (.leaf (-31))) (.branch 56 (.leaf (-30)) (.leaf (-29)))) (.branch 68 (.branch 64 (.leaf (-28)) (.leaf (-27))) (.branch 69 (.leaf (-18)) (.leaf (-9))))),
  (.branch 67 (.branch 55 (.leaf (-26)) (.branch 61 (.leaf (-25)) (.leaf (-24)))) (.branch 68 (.leaf (-18)) (.branch 69 (.leaf (-12)) (.leaf (-6))))),
  (.branch 67 (.branch 65 (.leaf (-8)) (.branch 66 (.leaf (-7)) (.leaf (-6)))) (.branch 68 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 67 (.branch 57 (.leaf (-21)) (.branch 66 (.leaf (-20)) (.leaf (-16)))) (.branch 68 (.leaf (-12)) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 65 (.branch 63 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 64 (.leaf (-13)) (.leaf (-12)))) (.branch 67 (.branch 66 (.leaf (-11)) (.leaf (-10))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-8)) (.leaf (-7)))))),
  (.branch 69 (.leaf (-4)) (.leaf (-3))),
  (.branch 63 (.branch 60 (.branch 34 (.leaf (-15)) (.branch 59 (.leaf (-14)) (.leaf (-13)))) (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-11)) (.leaf (-10))))) (.branch 66 (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7)))) (.branch 68 (.branch 67 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3))))))]
def witnessP9_284_4682 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (3))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (7)) (.leaf (4))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (1)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (5)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (0))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (4)) (.leaf (3)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (6)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (3)) (.leaf (0))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (2)) (.leaf (1))) (.branch 46 (.leaf (4)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (5)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 51 (.leaf (0)) (.leaf (3))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (8)) (.leaf (4))) (.branch 59 (.leaf (0)) (.branch 60 (.leaf (2)) (.leaf (1)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (3)) (.leaf (0))) (.branch 64 (.leaf (1)) (.leaf (5)))) (.branch 67 (.branch 66 (.leaf (2)) (.leaf (0))) (.branch 68 (.leaf (1)) (.branch 69 (.leaf (4)) (.leaf (3)))))))))
  code := certificateP9_4682
  counts := ![(.branch 32 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 51 (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.branch 47 (.leaf (12)) (.leaf (13))))) (.branch 59 (.branch 55 (.leaf (14)) (.leaf (15))) (.branch 63 (.leaf (16)) (.branch 67 (.leaf (17)) (.leaf (18))))))),
  (.branch 33 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))) (.branch 53 (.branch 41 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 45 (.leaf (11)) (.branch 49 (.leaf (12)) (.leaf (13))))) (.branch 61 (.branch 56 (.leaf (14)) (.leaf (15))) (.branch 64 (.leaf (16)) (.branch 68 (.leaf (17)) (.leaf (18))))))),
  (.branch 31 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 35 (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.branch 70 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 58 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 69 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 57 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-26)) (.leaf (-33)))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 56 (.leaf (-3)) (.leaf (-4)))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 54 (.leaf (-5)) (.leaf (-6)))),
  (.branch 35 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 42 (.leaf (-6)) (.leaf (-11)))),
  (.branch 11 (.leaf (0)) (.branch 34 (.leaf (-2)) (.leaf (-3)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-31))),
  (.branch 22 (.leaf (0)) (.leaf (-48))),
  (.branch 57 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 56 (.branch 48 (.branch 44 (.leaf (-33)) (.leaf (-32))) (.branch 52 (.leaf (-31)) (.leaf (-30)))) (.branch 64 (.branch 60 (.leaf (-29)) (.leaf (-28))) (.branch 68 (.leaf (-27)) (.branch 69 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 69 (.leaf (-4)) (.leaf (-3))),
  (.branch 68 (.branch 67 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3)))),
  (.branch 64 (.branch 53 (.branch 43 (.leaf (-11)) (.leaf (-10))) (.branch 63 (.leaf (-9)) (.leaf (-7)))) (.branch 66 (.branch 65 (.leaf (-5)) (.leaf (-3))) (.branch 67 (.leaf (-1)) (.leaf (0))))),
  (.leaf (-3)),
  (.branch 67 (.branch 66 (.leaf (-10)) (.leaf (-8))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2))))),
  (.branch 54 (.branch 46 (.branch 42 (.branch 40 (.leaf (-31)) (.branch 41 (.leaf (-30)) (.leaf (-29)))) (.branch 44 (.branch 43 (.leaf (-28)) (.leaf (-27))) (.branch 45 (.leaf (-26)) (.leaf (-25))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-24)) (.leaf (-23))) (.branch 49 (.leaf (-22)) (.leaf (-21)))) (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-19))) (.branch 53 (.leaf (-18)) (.leaf (-17)))))) (.branch 62 (.branch 58 (.branch 56 (.branch 55 (.leaf (-16)) (.leaf (-15))) (.branch 57 (.leaf (-14)) (.leaf (-13)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-11))) (.branch 61 (.leaf (-10)) (.leaf (-9))))) (.branch 66 (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 34 (.branch 28 (.branch 25 (.branch 23 (.leaf (-48)) (.branch 24 (.leaf (-47)) (.leaf (-46)))) (.branch 26 (.leaf (-45)) (.branch 27 (.leaf (-44)) (.leaf (-43))))) (.branch 31 (.branch 29 (.leaf (-42)) (.branch 30 (.leaf (-41)) (.leaf (-40)))) (.branch 32 (.leaf (-39)) (.branch 33 (.leaf (-38)) (.leaf (-37)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (-36)) (.branch 36 (.leaf (-35)) (.leaf (-34)))) (.branch 38 (.leaf (-33)) (.branch 39 (.leaf (-32)) (.leaf (-31))))) (.branch 43 (.branch 41 (.leaf (-30)) (.branch 42 (.leaf (-29)) (.leaf (-28)))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-26)) (.leaf (-25))))))) (.branch 58 (.branch 52 (.branch 49 (.branch 47 (.leaf (-24)) (.branch 48 (.leaf (-23)) (.leaf (-22)))) (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-20)) (.leaf (-19))))) (.branch 55 (.branch 53 (.leaf (-18)) (.branch 54 (.leaf (-17)) (.leaf (-16)))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-14)) (.leaf (-13)))))) (.branch 64 (.branch 61 (.branch 59 (.leaf (-12)) (.branch 60 (.leaf (-11)) (.leaf (-10)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-8)) (.leaf (-7))))) (.branch 67 (.branch 65 (.leaf (-6)) (.branch 66 (.leaf (-5)) (.leaf (-4)))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 63 (.branch 60 (.branch 58 (.leaf (-13)) (.branch 59 (.leaf (-12)) (.leaf (-11)))) (.branch 61 (.leaf (-10)) (.branch 62 (.leaf (-9)) (.leaf (-8))))) (.branch 66 (.branch 64 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_284_4683 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (8))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (1))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (7)) (.leaf (0))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (3))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (1)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (8)) (.leaf (3)))) (.branch 32 (.branch 31 (.leaf (5)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (4)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (3)) (.leaf (6)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (7))) (.branch 42 (.leaf (2)) (.leaf (1))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (4))) (.branch 46 (.leaf (3)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (5)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 51 (.leaf (8)) (.leaf (0))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (3))) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (6)) (.leaf (2))) (.branch 59 (.leaf (0)) (.branch 60 (.leaf (4)) (.leaf (1)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (3)) (.leaf (0))) (.branch 64 (.leaf (7)) (.leaf (2)))) (.branch 67 (.branch 66 (.leaf (5)) (.leaf (1))) (.branch 68 (.leaf (0)) (.branch 69 (.leaf (3)) (.leaf (4)))))))))
  code := certificateP9_4683
  counts := ![(.branch 33 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 52 (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.branch 47 (.leaf (12)) (.leaf (13))))) (.branch 59 (.branch 56 (.leaf (14)) (.leaf (15))) (.branch 63 (.leaf (16)) (.branch 68 (.leaf (17)) (.leaf (18))))))),
  (.branch 32 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 61 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 67 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 38 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 46 (.leaf (5)) (.leaf (6))) (.branch 62 (.leaf (7)) (.branch 69 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.branch 70 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 41 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 47 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-23))),
  (.branch 34 (.branch 3 (.leaf (0)) (.leaf (-43))) (.branch 65 (.leaf (-44)) (.leaf (-45)))),
  (.branch 7 (.leaf (0)) (.branch 30 (.leaf (-7)) (.leaf (-10)))),
  (.branch 25 (.branch 18 (.leaf (0)) (.leaf (-2))) (.branch 53 (.leaf (-7)) (.branch 60 (.leaf (-8)) (.leaf (-13))))),
  (.branch 13 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-27))),
  (.branch 16 (.leaf (0)) (.leaf (-8))),
  (.branch 29 (.branch 6 (.leaf (0)) (.leaf (-18))) (.branch 51 (.leaf (-19)) (.leaf (-21))))]
  high := ![(.branch 64 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-3)))),
  (.branch 56 (.branch 44 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 50 (.leaf (-21)) (.leaf (-20)))) (.branch 68 (.branch 62 (.leaf (-19)) (.leaf (-18))) (.branch 69 (.leaf (-12)) (.leaf (-6))))),
  (.branch 67 (.branch 66 (.leaf (-45)) (.leaf (-36))) (.branch 68 (.leaf (-27)) (.branch 69 (.leaf (-18)) (.leaf (-9))))),
  (.branch 31 (.leaf (-10)) (.leaf (-9))),
  (.branch 64 (.branch 62 (.branch 61 (.leaf (-13)) (.leaf (-11))) (.branch 63 (.leaf (-9)) (.leaf (-7)))) (.branch 66 (.branch 65 (.leaf (-5)) (.leaf (-3))) (.branch 67 (.leaf (-1)) (.leaf (0))))),
  (.branch 67 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2))))),
  (.branch 63 (.branch 59 (.branch 40 (.leaf (-27)) (.branch 58 (.leaf (-26)) (.leaf (-24)))) (.branch 61 (.branch 60 (.leaf (-22)) (.leaf (-20))) (.branch 62 (.leaf (-18)) (.leaf (-16))))) (.branch 66 (.branch 64 (.leaf (-14)) (.branch 65 (.leaf (-12)) (.leaf (-10)))) (.branch 68 (.branch 67 (.leaf (-8)) (.leaf (-6))) (.branch 69 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 67 (.branch 65 (.leaf (-8)) (.branch 66 (.leaf (-7)) (.leaf (-6)))) (.branch 68 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-3))))),
  (.branch 60 (.branch 55 (.branch 53 (.branch 52 (.leaf (-21)) (.leaf (-20))) (.branch 54 (.leaf (-19)) (.leaf (-18)))) (.branch 57 (.branch 56 (.leaf (-17)) (.leaf (-16))) (.branch 58 (.leaf (-15)) (.branch 59 (.leaf (-14)) (.leaf (-13)))))) (.branch 65 (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-11))) (.branch 63 (.leaf (-10)) (.branch 64 (.leaf (-9)) (.leaf (-8))))) (.branch 67 (.branch 66 (.leaf (-7)) (.leaf (-6))) (.branch 68 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-3)))))))]
def witnessP9_284_4684 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (2)) (.leaf (0))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (4))) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (6)) (.leaf (1)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (4)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (1)) (.leaf (5)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (3)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (4))) (.branch 42 (.leaf (1)) (.leaf (8))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (2))) (.branch 46 (.leaf (1)) (.leaf (3)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (5)) (.branch 51 (.leaf (2)) (.leaf (0))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (4))) (.branch 55 (.leaf (0)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (1))) (.branch 59 (.leaf (0)) (.branch 60 (.leaf (6)) (.leaf (1)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (2)) (.leaf (0))) (.branch 64 (.leaf (3)) (.leaf (1)))) (.branch 67 (.branch 66 (.leaf (4)) (.leaf (0))) (.branch 68 (.leaf (2)) (.branch 69 (.leaf (1)) (.leaf (5)))))))))
  code := certificateP9_4684
  counts := ![(.branch 32 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 52 (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.branch 48 (.leaf (12)) (.leaf (13))))) (.branch 59 (.branch 55 (.leaf (14)) (.leaf (15))) (.branch 63 (.leaf (16)) (.branch 67 (.leaf (17)) (.leaf (18))))))),
  (.branch 34 (.branch 14 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))) (.branch 53 (.branch 42 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.branch 49 (.leaf (12)) (.leaf (13))))) (.branch 61 (.branch 58 (.leaf (14)) (.leaf (15))) (.branch 65 (.leaf (16)) (.branch 69 (.leaf (17)) (.leaf (18))))))),
  (.branch 33 (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 57 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 70 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.leaf (0)) (.branch 60 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-26)) (.leaf (-30)))),
  (.branch 2 (.leaf (0)) (.branch 37 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-11)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-23)) (.leaf (-24)))),
  (.branch 6 (.leaf (0)) (.branch 41 (.leaf (-6)) (.leaf (-7)))),
  (.branch 15 (.leaf (0)) (.branch 50 (.leaf (-4)) (.leaf (-7)))),
  (.branch 25 (.leaf (0)) (.leaf (-10))),
  (.branch 8 (.leaf (0)) (.leaf (-62))),
  (.branch 43 (.leaf (0)) (.leaf (-27)))]
  high := ![(.branch 64 (.branch 56 (.leaf (-30)) (.branch 60 (.leaf (-29)) (.leaf (-28)))) (.branch 68 (.leaf (-27)) (.branch 69 (.leaf (-18)) (.leaf (-9))))),
  (.leaf (-3)),
  (.branch 63 (.leaf (-13)) (.branch 69 (.leaf (-12)) (.leaf (-6)))),
  (.branch 67 (.branch 65 (.leaf (-24)) (.branch 66 (.leaf (-20)) (.leaf (-16)))) (.branch 68 (.leaf (-12)) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 67 (.branch 42 (.leaf (-7)) (.leaf (-6))) (.branch 68 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-3))))),
  (.branch 54 (.branch 52 (.branch 51 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.branch 55 (.leaf (-3)) (.leaf (-2))) (.branch 57 (.leaf (-1)) (.leaf (0))))),
  (.branch 65 (.branch 62 (.branch 61 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-8)) (.branch 64 (.leaf (-7)) (.leaf (-6))))) (.branch 67 (.branch 66 (.leaf (-5)) (.leaf (-4))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 23 (.branch 15 (.branch 11 (.branch 9 (.leaf (-62)) (.branch 10 (.leaf (-61)) (.leaf (-60)))) (.branch 13 (.branch 12 (.leaf (-59)) (.leaf (-58))) (.branch 14 (.leaf (-57)) (.leaf (-56))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-55)) (.leaf (-54))) (.branch 18 (.leaf (-53)) (.leaf (-52)))) (.branch 21 (.branch 20 (.leaf (-51)) (.leaf (-50))) (.branch 22 (.leaf (-49)) (.leaf (-48)))))) (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-47)) (.leaf (-46))) (.branch 26 (.leaf (-45)) (.leaf (-44)))) (.branch 29 (.branch 28 (.leaf (-43)) (.leaf (-42))) (.branch 30 (.leaf (-41)) (.leaf (-40))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-39)) (.leaf (-38))) (.branch 34 (.leaf (-37)) (.leaf (-36)))) (.branch 37 (.branch 36 (.leaf (-35)) (.leaf (-34))) (.branch 38 (.leaf (-33)) (.leaf (-32))))))) (.branch 54 (.branch 46 (.branch 42 (.branch 40 (.leaf (-31)) (.branch 41 (.leaf (-30)) (.leaf (-29)))) (.branch 44 (.branch 43 (.leaf (-28)) (.leaf (-27))) (.branch 45 (.leaf (-26)) (.leaf (-25))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-24)) (.leaf (-23))) (.branch 49 (.leaf (-22)) (.leaf (-21)))) (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-19))) (.branch 53 (.leaf (-18)) (.leaf (-17)))))) (.branch 62 (.branch 58 (.branch 56 (.branch 55 (.leaf (-16)) (.leaf (-15))) (.branch 57 (.leaf (-14)) (.leaf (-13)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-11))) (.branch 61 (.leaf (-10)) (.leaf (-9))))) (.branch 66 (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 56 (.branch 49 (.branch 46 (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-26)) (.leaf (-25)))) (.branch 47 (.leaf (-24)) (.branch 48 (.leaf (-23)) (.leaf (-22))))) (.branch 52 (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-20)) (.leaf (-19)))) (.branch 54 (.branch 53 (.leaf (-18)) (.leaf (-17))) (.branch 55 (.leaf (-16)) (.leaf (-15)))))) (.branch 63 (.branch 59 (.branch 57 (.leaf (-14)) (.branch 58 (.leaf (-13)) (.leaf (-12)))) (.branch 61 (.branch 60 (.leaf (-11)) (.leaf (-10))) (.branch 62 (.leaf (-9)) (.leaf (-8))))) (.branch 66 (.branch 64 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_284_4685 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (2)) (.leaf (1))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (2)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (3)) (.leaf (2)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (8))) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (2))) (.branch 33 (.leaf (6)) (.branch 34 (.leaf (4)) (.leaf (1)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (3)) (.leaf (1)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (5))) (.branch 42 (.leaf (2)) (.leaf (4))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (3)) (.leaf (7)))) (.branch 49 (.branch 48 (.leaf (2)) (.leaf (0))) (.branch 50 (.leaf (6)) (.branch 51 (.leaf (1)) (.leaf (2))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (3))) (.branch 55 (.leaf (1)) (.leaf (4)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (5)) (.branch 60 (.leaf (3)) (.leaf (1)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (0)) (.leaf (8))) (.branch 64 (.leaf (2)) (.leaf (3)))) (.branch 67 (.branch 66 (.leaf (0)) (.leaf (1))) (.branch 68 (.leaf (6)) (.branch 69 (.leaf (4)) (.leaf (2)))))))))
  code := certificateP9_4685
  counts := ![(.branch 31 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 49 (.branch 40 (.branch 36 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 57 (.branch 53 (.leaf (12)) (.leaf (13))) (.branch 62 (.leaf (14)) (.branch 66 (.leaf (15)) (.leaf (16))))))),
  (.branch 35 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))) (.branch 51 (.branch 39 (.leaf (7)) (.branch 45 (.leaf (8)) (.leaf (9)))) (.branch 61 (.branch 55 (.leaf (10)) (.leaf (11))) (.branch 67 (.leaf (12)) (.leaf (13)))))),
  (.branch 37 (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))) (.branch 52 (.branch 42 (.leaf (7)) (.branch 48 (.leaf (8)) (.leaf (9)))) (.branch 64 (.branch 58 (.leaf (10)) (.leaf (11))) (.branch 70 (.leaf (12)) (.leaf (13)))))),
  (.branch 30 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 38 (.leaf (5)) (.branch 46 (.leaf (6)) (.leaf (7)))) (.branch 60 (.leaf (8)) (.branch 65 (.leaf (9)) (.leaf (10)))))),
  (.branch 34 (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 69 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 68 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 63 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-27))) (.branch 9 (.leaf (-30)) (.branch 22 (.leaf (-33)) (.leaf (-34))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))) (.branch 39 (.leaf (-17)) (.branch 55 (.leaf (-19)) (.leaf (-22))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 42 (.leaf (-8)) (.branch 52 (.leaf (-10)) (.leaf (-14))))),
  (.branch 30 (.branch 3 (.leaf (0)) (.branch 25 (.leaf (-14)) (.leaf (-17)))) (.branch 60 (.leaf (-25)) (.branch 65 (.leaf (-27)) (.leaf (-35))))),
  (.branch 8 (.leaf (0)) (.branch 43 (.leaf (-9)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.leaf (-23))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-23))),
  (.branch 28 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 67 (.branch 58 (.leaf (-34)) (.leaf (-32))) (.branch 68 (.leaf (-24)) (.branch 69 (.leaf (-16)) (.leaf (-8))))),
  (.branch 62 (.branch 56 (.leaf (-22)) (.leaf (-21))) (.branch 68 (.leaf (-20)) (.branch 69 (.leaf (-17)) (.leaf (-14))))),
  (.branch 65 (.branch 53 (.leaf (-14)) (.branch 59 (.leaf (-13)) (.leaf (-12)))) (.branch 67 (.branch 66 (.leaf (-9)) (.leaf (-6))) (.branch 68 (.leaf (-3)) (.leaf (0))))),
  (.branch 67 (.branch 66 (.leaf (-35)) (.leaf (-32))) (.branch 68 (.leaf (-29)) (.branch 69 (.leaf (-26)) (.leaf (-23))))),
  (.branch 44 (.leaf (-14)) (.branch 57 (.leaf (-13)) (.leaf (-12)))),
  (.branch 64 (.branch 61 (.branch 42 (.leaf (-23)) (.branch 60 (.leaf (-22)) (.leaf (-20)))) (.branch 62 (.leaf (-18)) (.branch 63 (.leaf (-16)) (.leaf (-14))))) (.branch 67 (.branch 65 (.leaf (-12)) (.branch 66 (.leaf (-10)) (.leaf (-8)))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 51 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-2)))),
  (.branch 58 (.branch 52 (.branch 49 (.branch 48 (.leaf (-23)) (.leaf (-22))) (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-20)) (.leaf (-19))))) (.branch 55 (.branch 53 (.leaf (-18)) (.branch 54 (.leaf (-17)) (.leaf (-16)))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-14)) (.leaf (-13)))))) (.branch 64 (.branch 61 (.branch 59 (.leaf (-12)) (.branch 60 (.leaf (-11)) (.leaf (-10)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-8)) (.leaf (-7))))) (.branch 67 (.branch 65 (.leaf (-6)) (.branch 66 (.leaf (-5)) (.leaf (-4)))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 66 (.branch 64 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_284_4686 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (7))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (8))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (0))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (1)) (.leaf (4)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (3)) (.leaf (7)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (5)) (.leaf (4)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (3)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (8))) (.branch 42 (.leaf (4)) (.leaf (1))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (6)) (.leaf (0))) (.branch 46 (.leaf (5)) (.leaf (3)))) (.branch 49 (.branch 48 (.leaf (2)) (.leaf (1))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (4)) (.leaf (7))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (5)) (.leaf (0))) (.branch 59 (.leaf (2)) (.branch 60 (.leaf (1)) (.leaf (4)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (0)) (.leaf (6))) (.branch 64 (.leaf (3)) (.leaf (8)))) (.branch 67 (.branch 66 (.leaf (1)) (.leaf (0))) (.branch 68 (.leaf (2)) (.branch 69 (.leaf (5)) (.leaf (4)))))))))
  code := certificateP9_4686
  counts := ![(.branch 32 (.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 50 (.branch 40 (.branch 36 (.leaf (8)) (.leaf (9))) (.branch 45 (.leaf (10)) (.leaf (11)))) (.branch 58 (.branch 54 (.leaf (12)) (.leaf (13))) (.branch 62 (.leaf (14)) (.branch 67 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 39 (.leaf (5)) (.branch 48 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.branch 70 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 69 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 27 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))) (.branch 40 (.leaf (-9)) (.branch 62 (.leaf (-10)) (.leaf (-11))))),
  (.branch 2 (.leaf (0)) (.branch 25 (.leaf (-23)) (.leaf (-25)))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 18 (.leaf (-4)) (.leaf (-6)))) (.branch 53 (.branch 39 (.leaf (-8)) (.leaf (-9))) (.branch 59 (.leaf (-11)) (.leaf (-13))))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-23)) (.leaf (-24)))),
  (.branch 7 (.leaf (0)) (.branch 42 (.leaf (-2)) (.leaf (-3)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-2)) (.leaf (-4)))),
  (.branch 9 (.leaf (0)) (.branch 44 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.branch 52 (.leaf (-35)) (.leaf (-37)))),
  (.branch 17 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 68 (.branch 63 (.leaf (-11)) (.leaf (-10))) (.branch 69 (.leaf (-8)) (.leaf (-6)))),
  (.branch 67 (.branch 61 (.leaf (-25)) (.leaf (-24))) (.branch 68 (.leaf (-18)) (.branch 69 (.leaf (-12)) (.leaf (-6))))),
  (.branch 60 (.leaf (-13)) (.branch 69 (.leaf (-12)) (.leaf (-11)))),
  (.branch 67 (.branch 65 (.leaf (-24)) (.branch 66 (.leaf (-20)) (.leaf (-16)))) (.branch 68 (.leaf (-12)) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 62 (.branch 52 (.leaf (-3)) (.leaf (-2))) (.branch 63 (.leaf (-1)) (.leaf (0)))),
  (.branch 58 (.leaf (-4)) (.leaf (-3))),
  (.branch 66 (.branch 64 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-7)))) (.branch 68 (.branch 67 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3))))),
  (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (-37)) (.leaf (-35))) (.branch 55 (.leaf (-33)) (.leaf (-31)))) (.branch 58 (.branch 57 (.leaf (-29)) (.leaf (-27))) (.branch 59 (.leaf (-25)) (.branch 60 (.leaf (-23)) (.leaf (-21)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (-19)) (.leaf (-17))) (.branch 64 (.leaf (-15)) (.leaf (-13)))) (.branch 67 (.branch 66 (.leaf (-11)) (.leaf (-9))) (.branch 68 (.leaf (-7)) (.branch 69 (.leaf (-5)) (.leaf (-3))))))),
  (.branch 66 (.branch 18 (.leaf (-13)) (.branch 42 (.leaf (-12)) (.leaf (-11)))) (.branch 68 (.branch 67 (.leaf (-9)) (.leaf (-7))) (.branch 69 (.leaf (-5)) (.leaf (-3)))))]
def witnessP9_284_4687 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (7))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (6))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (1))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (8)) (.branch 25 (.leaf (1)) (.leaf (0)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (3)) (.leaf (6))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (4))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (5)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (3)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (7))) (.branch 42 (.leaf (6)) (.leaf (1))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (4))) (.branch 46 (.leaf (1)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (2)) (.leaf (5))) (.branch 50 (.leaf (3)) (.branch 51 (.leaf (0)) (.leaf (1))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (6)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (8)) (.branch 60 (.leaf (1)) (.leaf (0)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (3)) (.leaf (5))) (.branch 64 (.leaf (1)) (.leaf (0)))) (.branch 67 (.branch 66 (.leaf (2)) (.leaf (4))) (.branch 68 (.leaf (0)) (.branch 69 (.leaf (1)) (.leaf (6)))))))))
  code := certificateP9_4687
  counts := ![(.branch 33 (.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))) (.branch 51 (.branch 40 (.branch 36 (.leaf (10)) (.leaf (11))) (.branch 44 (.leaf (12)) (.branch 47 (.leaf (13)) (.leaf (14))))) (.branch 61 (.branch 54 (.leaf (15)) (.branch 58 (.leaf (16)) (.leaf (17)))) (.branch 65 (.leaf (18)) (.branch 68 (.leaf (19)) (.leaf (20))))))),
  (.branch 34 (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 52 (.branch 43 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 60 (.branch 55 (.leaf (12)) (.leaf (13))) (.branch 64 (.leaf (14)) (.branch 69 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 67 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 42 (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 56 (.leaf (3)) (.branch 70 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 59 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 29 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 20 (.leaf (-4)) (.leaf (-5)))) (.branch 46 (.branch 37 (.leaf (-6)) (.leaf (-8))) (.branch 55 (.leaf (-9)) (.branch 64 (.leaf (-10)) (.leaf (-11)))))),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 3 (.leaf (0)) (.leaf (-26))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (-3))) (.branch 53 (.leaf (-8)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-29))),
  (.branch 24 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 37 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-11)),
  (.branch 58 (.branch 40 (.leaf (-19)) (.branch 49 (.leaf (-18)) (.leaf (-17)))) (.branch 68 (.branch 67 (.leaf (-16)) (.leaf (-12))) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 65 (.branch 51 (.branch 39 (.leaf (-26)) (.leaf (-25))) (.branch 63 (.leaf (-24)) (.branch 64 (.leaf (-21)) (.leaf (-18))))) (.branch 67 (.branch 66 (.leaf (-15)) (.leaf (-12))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 68 (.branch 54 (.leaf (-12)) (.leaf (-11))) (.branch 69 (.leaf (-10)) (.leaf (-9)))),
  (.branch 66 (.branch 64 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 55 (.branch 48 (.branch 44 (.branch 42 (.leaf (-29)) (.branch 43 (.leaf (-28)) (.leaf (-27)))) (.branch 46 (.branch 45 (.leaf (-26)) (.leaf (-25))) (.branch 47 (.leaf (-24)) (.leaf (-23))))) (.branch 51 (.branch 49 (.leaf (-22)) (.branch 50 (.leaf (-21)) (.leaf (-20)))) (.branch 53 (.branch 52 (.leaf (-19)) (.leaf (-18))) (.branch 54 (.leaf (-17)) (.leaf (-16)))))) (.branch 62 (.branch 58 (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-14)) (.leaf (-13)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-11))) (.branch 61 (.leaf (-10)) (.leaf (-9))))) (.branch 66 (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 64 (.branch 61 (.branch 60 (.leaf (-11)) (.leaf (-10))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-8)) (.leaf (-7))))) (.branch 67 (.branch 65 (.leaf (-6)) (.branch 66 (.leaf (-5)) (.leaf (-4)))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_284_4688 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (6)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (5))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (2))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (8))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (6))) (.branch 20 (.leaf (0)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (3))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (7)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (4)) (.leaf (0))) (.branch 29 (.leaf (6)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (3)) (.leaf (0))) (.branch 33 (.leaf (5)) (.branch 34 (.leaf (1)) (.leaf (8)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (3)) (.leaf (4)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (6)) (.leaf (0))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (7)) (.leaf (5))) (.branch 46 (.leaf (2)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (3)) (.leaf (1))) (.branch 50 (.leaf (4)) (.branch 51 (.leaf (0)) (.leaf (8))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (6))) (.branch 55 (.leaf (0)) (.leaf (5)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (3))) (.branch 59 (.leaf (0)) (.branch 60 (.leaf (2)) (.leaf (7)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (4)) (.leaf (0))) (.branch 64 (.leaf (6)) (.leaf (1)))) (.branch 67 (.branch 66 (.leaf (3)) (.leaf (0))) (.branch 68 (.leaf (5)) (.branch 69 (.leaf (2)) (.leaf (8)))))))))
  code := certificateP9_4688
  counts := ![(.branch 32 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 51 (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.branch 47 (.leaf (12)) (.leaf (13))))) (.branch 59 (.branch 55 (.leaf (14)) (.leaf (15))) (.branch 63 (.leaf (16)) (.branch 67 (.leaf (17)) (.leaf (18))))))),
  (.branch 34 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 41 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 37 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 46 (.leaf (5)) (.leaf (6))) (.branch 60 (.leaf (7)) (.branch 69 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.branch 70 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-26)) (.leaf (-33)))),
  (.branch 2 (.leaf (0)) (.branch 25 (.leaf (-6)) (.leaf (-7)))),
  (.branch 37 (.branch 6 (.leaf (0)) (.leaf (-2))) (.branch 60 (.leaf (-3)) (.leaf (-4)))),
  (.branch 31 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 38 (.leaf (-14)) (.branch 66 (.leaf (-19)) (.leaf (-20))))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-23)) (.leaf (-25)))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (-5)) (.leaf (-7)))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 64 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (-17)) (.leaf (-18)))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 56 (.branch 48 (.branch 44 (.leaf (-33)) (.leaf (-32))) (.branch 52 (.leaf (-31)) (.leaf (-30)))) (.branch 64 (.branch 60 (.leaf (-29)) (.leaf (-28))) (.branch 68 (.leaf (-27)) (.branch 69 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 67 (.branch 66 (.leaf (-7)) (.leaf (-6))) (.branch 68 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-3))))),
  (.branch 61 (.leaf (-4)) (.leaf (-3))),
  (.branch 68 (.branch 67 (.leaf (-20)) (.leaf (-18))) (.branch 69 (.leaf (-16)) (.leaf (-14)))),
  (.branch 65 (.branch 63 (.branch 51 (.leaf (-25)) (.leaf (-24))) (.branch 64 (.leaf (-21)) (.leaf (-18)))) (.branch 67 (.branch 66 (.leaf (-15)) (.leaf (-12))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 57 (.leaf (-7)) (.branch 69 (.leaf (-6)) (.leaf (-3)))),
  (.branch 67 (.branch 65 (.leaf (-8)) (.branch 66 (.leaf (-7)) (.leaf (-6)))) (.branch 68 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-3))))),
  (.branch 65 (.branch 63 (.branch 62 (.leaf (-18)) (.leaf (-16))) (.branch 64 (.leaf (-14)) (.leaf (-12)))) (.branch 67 (.branch 66 (.leaf (-10)) (.leaf (-8))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 53 (.leaf (-1)) (.leaf (0)))]
def witnessP9_284_4689 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (7))) (.branch 11 (.leaf (6)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (0))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (5)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (8)) (.leaf (0))) (.branch 24 (.leaf (6)) (.branch 25 (.leaf (1)) (.leaf (4)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (5))) (.branch 33 (.leaf (7)) (.branch 34 (.leaf (2)) (.leaf (4)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (3)) (.leaf (6)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (2))) (.branch 42 (.leaf (4)) (.leaf (1))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (8))) (.branch 46 (.leaf (5)) (.leaf (3)))) (.branch 49 (.branch 48 (.leaf (2)) (.leaf (1))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (4)) (.leaf (0))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (6)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (7)) (.leaf (0))) (.branch 59 (.leaf (5)) (.branch 60 (.leaf (1)) (.leaf (4)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (2)) (.leaf (0))) (.branch 64 (.leaf (3)) (.leaf (0)))) (.branch 67 (.branch 66 (.leaf (1)) (.leaf (6))) (.branch 68 (.leaf (8)) (.branch 69 (.leaf (2)) (.leaf (4)))))))))
  code := certificateP9_4689
  counts := ![(.branch 30 (.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 50 (.branch 40 (.branch 36 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 58 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 63 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 55 (.branch 41 (.leaf (5)) (.branch 48 (.leaf (6)) (.leaf (7)))) (.branch 62 (.leaf (8)) (.branch 69 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.branch 70 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 53 (.leaf (3)) (.branch 67 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3)))),
  (.branch 45 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 68 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 9 (.leaf (-5)) (.leaf (-6)))) (.branch 44 (.branch 30 (.leaf (-8)) (.leaf (-10))) (.branch 52 (.leaf (-11)) (.branch 65 (.leaf (-13)) (.leaf (-15)))))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-23)) (.leaf (-26)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-23)) (.leaf (-24)))),
  (.branch 7 (.leaf (0)) (.branch 42 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 59 (.leaf (-10)) (.leaf (-11)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4)))),
  (.branch 10 (.leaf (0)) (.branch 33 (.leaf (-40)) (.leaf (-41)))),
  (.branch 45 (.branch 22 (.leaf (0)) (.leaf (-4))) (.branch 68 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 67 (.branch 66 (.leaf (-15)) (.leaf (-14))) (.branch 68 (.leaf (-13)) (.branch 69 (.leaf (-12)) (.leaf (-11))))),
  (.branch 67 (.branch 55 (.leaf (-26)) (.branch 61 (.leaf (-25)) (.leaf (-24)))) (.branch 68 (.leaf (-18)) (.branch 69 (.leaf (-12)) (.leaf (-6))))),
  (.leaf (-1)),
  (.branch 67 (.branch 65 (.leaf (-24)) (.branch 66 (.leaf (-20)) (.leaf (-16)))) (.branch 68 (.leaf (-12)) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 62 (.branch 52 (.leaf (-3)) (.leaf (-2))) (.branch 63 (.leaf (-1)) (.leaf (0)))),
  (.branch 64 (.branch 61 (.branch 60 (.leaf (-11)) (.leaf (-10))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-8)) (.leaf (-7))))) (.branch 67 (.branch 65 (.leaf (-6)) (.branch 66 (.leaf (-5)) (.leaf (-4)))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 68 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1)))),
  (.branch 63 (.branch 59 (.branch 34 (.leaf (-41)) (.branch 58 (.leaf (-39)) (.leaf (-36)))) (.branch 61 (.branch 60 (.leaf (-33)) (.leaf (-30))) (.branch 62 (.leaf (-27)) (.leaf (-24))))) (.branch 66 (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-18)) (.leaf (-15)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-9))) (.branch 69 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 69 (.leaf (-6)) (.leaf (-3)))]
def witnessP9_284_4690 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (2)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (8)) (.leaf (0))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (6))) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (2))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (1)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (7)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (6)) (.leaf (0))) (.branch 33 (.leaf (5)) (.branch 34 (.leaf (1)) (.leaf (4)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (3)) (.leaf (8)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (6))) (.branch 42 (.leaf (1)) (.leaf (4))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (5))) (.branch 46 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (4)) (.branch 51 (.leaf (7)) (.leaf (0))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (6))) (.branch 55 (.leaf (0)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (5)) (.leaf (1))) (.branch 59 (.leaf (0)) (.branch 60 (.leaf (4)) (.leaf (2)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (8)) (.leaf (0))) (.branch 64 (.leaf (3)) (.leaf (1)))) (.branch 67 (.branch 66 (.leaf (6)) (.leaf (0))) (.branch 68 (.leaf (5)) (.branch 69 (.leaf (2)) (.leaf (4)))))))))
  code := certificateP9_4690
  counts := ![(.branch 32 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 52 (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.branch 48 (.leaf (12)) (.leaf (13))))) (.branch 59 (.branch 55 (.leaf (14)) (.leaf (15))) (.branch 63 (.leaf (16)) (.branch 67 (.leaf (17)) (.leaf (18))))))),
  (.branch 34 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 37 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 46 (.leaf (5)) (.leaf (6))) (.branch 61 (.leaf (7)) (.branch 69 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.branch 70 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-26)) (.leaf (-30)))),
  (.branch 2 (.leaf (0)) (.branch 49 (.leaf (-6)) (.leaf (-7)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 37 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-23)) (.leaf (-24)))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (-3))) (.branch 43 (.leaf (-8)) (.branch 50 (.leaf (-9)) (.leaf (-14))))),
  (.branch 10 (.leaf (0)) (.branch 33 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 41 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-58)) (.leaf (-59)))),
  (.branch 39 (.branch 16 (.leaf (0)) (.leaf (-22))) (.branch 62 (.leaf (-23)) (.leaf (-24))))]
  high := ![(.branch 64 (.branch 56 (.leaf (-30)) (.branch 60 (.leaf (-29)) (.leaf (-28)))) (.branch 68 (.leaf (-27)) (.branch 69 (.leaf (-18)) (.leaf (-9))))),
  (.branch 67 (.branch 66 (.leaf (-7)) (.leaf (-6))) (.branch 68 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 67 (.branch 65 (.leaf (-24)) (.branch 66 (.leaf (-20)) (.leaf (-16)))) (.branch 68 (.leaf (-12)) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 63 (.branch 61 (.branch 51 (.leaf (-14)) (.leaf (-13))) (.branch 62 (.leaf (-11)) (.leaf (-9)))) (.branch 65 (.branch 64 (.leaf (-7)) (.leaf (-5))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-1)) (.leaf (0)))))),
  (.branch 69 (.leaf (-6)) (.leaf (-3))),
  (.branch 67 (.branch 42 (.leaf (-7)) (.leaf (-6))) (.branch 68 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-3))))),
  (.branch 60 (.branch 55 (.branch 52 (.branch 28 (.leaf (-59)) (.leaf (-57))) (.branch 53 (.leaf (-54)) (.branch 54 (.leaf (-51)) (.leaf (-48))))) (.branch 57 (.branch 56 (.leaf (-45)) (.leaf (-42))) (.branch 58 (.leaf (-39)) (.branch 59 (.leaf (-36)) (.leaf (-33)))))) (.branch 65 (.branch 62 (.branch 61 (.leaf (-30)) (.leaf (-27))) (.branch 63 (.leaf (-24)) (.branch 64 (.leaf (-21)) (.leaf (-18))))) (.branch 67 (.branch 66 (.leaf (-15)) (.leaf (-12))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 66 (.branch 64 (.branch 63 (.leaf (-24)) (.leaf (-21))) (.branch 65 (.leaf (-18)) (.leaf (-15)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-9))) (.branch 69 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_284_4691 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (5))) (.branch 11 (.leaf (3)) (.leaf (8)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (1)) (.leaf (6))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (1))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (0)) (.leaf (8)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (6))) (.branch 29 (.leaf (3)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (7))) (.branch 33 (.leaf (4)) (.branch 34 (.leaf (5)) (.leaf (2)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (3)) (.leaf (8)))) (.branch 41 (.branch 40 (.leaf (6)) (.leaf (2))) (.branch 42 (.leaf (0)) (.leaf (4))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (1)) (.leaf (5))) (.branch 46 (.leaf (3)) (.leaf (7)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (2))) (.branch 50 (.leaf (4)) (.branch 51 (.leaf (1)) (.leaf (6))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (8)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (5)) (.leaf (1))) (.branch 59 (.leaf (4)) (.branch 60 (.leaf (0)) (.leaf (7)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (2)) (.leaf (6))) (.branch 64 (.leaf (3)) (.leaf (1)))) (.branch 67 (.branch 66 (.leaf (0)) (.leaf (8))) (.branch 68 (.leaf (4)) (.branch 69 (.leaf (5)) (.leaf (2)))))))))
  code := certificateP9_4691
  counts := ![(.branch 31 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 65 (.leaf (9)) (.leaf (10)))))),
  (.branch 35 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 56 (.branch 41 (.leaf (5)) (.branch 49 (.leaf (6)) (.leaf (7)))) (.branch 62 (.leaf (8)) (.branch 70 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 69 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 61 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 53 (.leaf (3)) (.branch 67 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-29))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-23)) (.leaf (-26)))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (-1))) (.branch 50 (.leaf (-3)) (.leaf (-4)))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-20)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 12 (.leaf (0)) (.branch 39 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 55 (.branch 43 (.branch 37 (.leaf (-29)) (.leaf (-28))) (.branch 49 (.leaf (-27)) (.leaf (-26)))) (.branch 67 (.branch 61 (.leaf (-25)) (.leaf (-24))) (.branch 68 (.leaf (-18)) (.branch 69 (.leaf (-12)) (.leaf (-6)))))),
  (.branch 67 (.branch 66 (.leaf (-5)) (.leaf (-4))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.branch 63 (.leaf (-1)) (.leaf (0))),
  (.branch 66 (.branch 56 (.branch 47 (.leaf (-26)) (.leaf (-25))) (.branch 65 (.leaf (-24)) (.leaf (-20)))) (.branch 68 (.branch 67 (.leaf (-16)) (.leaf (-12))) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 69 (.leaf (-4)) (.leaf (-3))),
  (.branch 46 (.leaf (-5)) (.branch 58 (.leaf (-4)) (.leaf (-3)))),
  (.branch 66 (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-18)) (.leaf (-15)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-9))) (.branch 69 (.leaf (-6)) (.leaf (-3))))),
  (.branch 65 (.branch 62 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-8)) (.branch 64 (.leaf (-7)) (.leaf (-6))))) (.branch 67 (.branch 66 (.leaf (-5)) (.leaf (-4))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_284_4692 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (5))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (7)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (4))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (3)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (8)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (1)) (.leaf (0)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (6)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (3)))) (.branch 32 (.branch 31 (.leaf (4)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (7)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (5)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (3))) (.branch 42 (.leaf (1)) (.leaf (0))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (6)) (.leaf (4))) (.branch 46 (.leaf (2)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (8)) (.leaf (1))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (2)) (.leaf (5))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (7)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (4)) (.branch 60 (.leaf (1)) (.leaf (0)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (6)) (.leaf (2))) (.branch 64 (.leaf (0)) (.leaf (3)))) (.branch 67 (.branch 66 (.leaf (5)) (.leaf (1))) (.branch 68 (.leaf (0)) (.branch 69 (.leaf (2)) (.leaf (8)))))))))
  code := certificateP9_4692
  counts := ![(.branch 33 (.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))) (.branch 50 (.branch 39 (.branch 36 (.leaf (10)) (.leaf (11))) (.branch 43 (.leaf (12)) (.branch 47 (.leaf (13)) (.leaf (14))))) (.branch 61 (.branch 54 (.leaf (15)) (.branch 57 (.leaf (16)) (.leaf (17)))) (.branch 64 (.leaf (18)) (.branch 68 (.leaf (19)) (.leaf (20))))))),
  (.branch 32 (.branch 14 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 67 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))) (.branch 63 (.branch 58 (.leaf (9)) (.leaf (10))) (.branch 69 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 66 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 35 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 48 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 70 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 42 (.leaf (-5)) (.leaf (-6)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 51 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-17))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 35 (.branch 13 (.leaf (0)) (.leaf (-13))) (.branch 56 (.leaf (-17)) (.leaf (-22)))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 65 (.branch 40 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-2)))),
  (.branch 68 (.branch 61 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 66 (.branch 42 (.leaf (-17)) (.branch 54 (.leaf (-16)) (.leaf (-15)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-9))) (.branch 69 (.leaf (-6)) (.leaf (-3))))),
  (.branch 64 (.branch 61 (.branch 60 (.leaf (-11)) (.leaf (-10))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-8)) (.leaf (-7))))) (.branch 67 (.branch 65 (.leaf (-6)) (.branch 66 (.leaf (-5)) (.leaf (-4)))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1)))),
  (.branch 65 (.branch 63 (.branch 45 (.leaf (-17)) (.leaf (-16))) (.branch 64 (.leaf (-14)) (.leaf (-12)))) (.branch 67 (.branch 66 (.leaf (-10)) (.leaf (-8))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 63 (.branch 59 (.branch 57 (.leaf (-22)) (.branch 58 (.leaf (-21)) (.leaf (-20)))) (.branch 61 (.branch 60 (.leaf (-19)) (.leaf (-18))) (.branch 62 (.leaf (-17)) (.leaf (-16))))) (.branch 66 (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-14)) (.leaf (-13)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-11))) (.branch 69 (.leaf (-10)) (.leaf (-9)))))),
  (.branch 50 (.branch 22 (.leaf (-5)) (.branch 49 (.leaf (-4)) (.leaf (-3)))) (.branch 51 (.leaf (-2)) (.branch 52 (.leaf (-1)) (.leaf (0)))))]
def witnessP9_284_4693 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (6))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (7))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (8)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (1))) (.branch 24 (.leaf (6)) (.branch 25 (.leaf (0)) (.leaf (3)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (4)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (7)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (5)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (4)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (6))) (.branch 42 (.leaf (0)) (.leaf (3))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (1)) (.leaf (8))) (.branch 46 (.leaf (0)) (.leaf (5)))) (.branch 49 (.branch 48 (.leaf (2)) (.leaf (0))) (.branch 50 (.leaf (4)) (.branch 51 (.leaf (1)) (.leaf (3))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (7)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (5)) (.leaf (1))) (.branch 59 (.leaf (6)) (.branch 60 (.leaf (0)) (.leaf (3)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (4)) (.leaf (2))) (.branch 64 (.leaf (0)) (.leaf (1)))) (.branch 67 (.branch 66 (.leaf (8)) (.leaf (0))) (.branch 68 (.leaf (2)) (.branch 69 (.leaf (3)) (.leaf (5)))))))))
  code := certificateP9_4693
  counts := ![(.branch 32 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))) (.branch 49 (.branch 39 (.branch 36 (.leaf (10)) (.leaf (11))) (.branch 42 (.leaf (12)) (.branch 46 (.leaf (13)) (.leaf (14))))) (.branch 60 (.branch 53 (.leaf (15)) (.branch 56 (.leaf (16)) (.leaf (17)))) (.branch 64 (.leaf (18)) (.branch 67 (.leaf (19)) (.leaf (20))))))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 65 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 40 (.leaf (5)) (.branch 48 (.leaf (6)) (.leaf (7)))) (.branch 63 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 34 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.branch 69 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 12 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 47 (.leaf (3)) (.leaf (4))) (.branch 70 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 45 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 33 (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-3)) (.leaf (-5)))) (.branch 54 (.branch 40 (.leaf (-7)) (.leaf (-8))) (.branch 68 (.leaf (-10)) (.leaf (-12))))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-26))),
  (.branch 22 (.leaf (0)) (.branch 57 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-23))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (-14)) (.leaf (-17)))),
  (.branch 20 (.leaf (0)) (.branch 66 (.leaf (-4)) (.leaf (-6))))]
  high := ![(.branch 68 (.branch 57 (.leaf (-7)) (.leaf (-6))) (.branch 69 (.leaf (-4)) (.leaf (-2)))),
  (.branch 67 (.branch 66 (.leaf (-5)) (.leaf (-4))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.branch 69 (.leaf (-12)) (.leaf (-11))),
  (.leaf (-4)),
  (.branch 65 (.branch 51 (.branch 39 (.leaf (-26)) (.leaf (-25))) (.branch 63 (.leaf (-24)) (.branch 64 (.leaf (-21)) (.leaf (-18))))) (.branch 67 (.branch 66 (.leaf (-15)) (.leaf (-12))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 59 (.branch 58 (.leaf (-3)) (.leaf (-2))) (.branch 60 (.leaf (-1)) (.leaf (0)))),
  (.branch 64 (.branch 61 (.branch 42 (.leaf (-23)) (.branch 60 (.leaf (-22)) (.leaf (-20)))) (.branch 62 (.leaf (-18)) (.branch 63 (.leaf (-16)) (.leaf (-14))))) (.branch 67 (.branch 65 (.leaf (-12)) (.branch 66 (.leaf (-10)) (.leaf (-8)))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 62 (.branch 58 (.branch 56 (.leaf (-17)) (.branch 57 (.leaf (-16)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-14)) (.leaf (-13))) (.branch 61 (.leaf (-12)) (.leaf (-11))))) (.branch 66 (.branch 64 (.branch 63 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-7)))) (.branch 68 (.branch 67 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 68 (.branch 67 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3))))]
def witnessP9_284_4694 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (7))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (8)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (5))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (1)) (.leaf (0)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (6)) (.leaf (2))) (.branch 29 (.leaf (4)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (7))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (2)) (.leaf (5)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (4)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (8))) (.branch 42 (.leaf (3)) (.leaf (1))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (6)) (.leaf (0))) (.branch 46 (.leaf (2)) (.leaf (4)))) (.branch 49 (.branch 48 (.leaf (5)) (.leaf (1))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (3)) (.leaf (2))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (7)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (4)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (5))) (.branch 59 (.leaf (3)) (.branch 60 (.leaf (1)) (.leaf (0)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (6)) (.leaf (2))) (.branch 64 (.leaf (4)) (.leaf (0)))) (.branch 67 (.branch 66 (.leaf (1)) (.leaf (8))) (.branch 68 (.leaf (3)) (.branch 69 (.leaf (2)) (.leaf (5)))))))))
  code := certificateP9_4694
  counts := ![(.branch 30 (.branch 10 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 50 (.branch 39 (.branch 36 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 61 (.branch 55 (.leaf (11)) (.leaf (12))) (.branch 65 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 52 (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))) (.branch 63 (.branch 57 (.leaf (9)) (.leaf (10))) (.branch 69 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 13 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 58 (.branch 48 (.leaf (3)) (.leaf (4))) (.branch 70 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 67 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 30 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-17)) (.leaf (-26)))) (.branch 39 (.leaf (-27)) (.branch 65 (.leaf (-33)) (.leaf (-34))))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-23)) (.leaf (-26)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (-5)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-7)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-23)) (.leaf (-24)))),
  (.branch 23 (.leaf (0)) (.branch 58 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 6 (.leaf (0)) (.branch 53 (.leaf (-19)) (.leaf (-22)))),
  (.branch 18 (.leaf (0)) (.branch 41 (.leaf (-7)) (.leaf (-9))))]
  high := ![(.branch 67 (.branch 66 (.leaf (-34)) (.leaf (-30))) (.branch 68 (.leaf (-26)) (.branch 69 (.leaf (-22)) (.leaf (-18))))),
  (.branch 67 (.branch 55 (.leaf (-26)) (.branch 61 (.leaf (-25)) (.leaf (-24)))) (.branch 68 (.leaf (-18)) (.branch 69 (.leaf (-12)) (.leaf (-6))))),
  (.branch 58 (.leaf (-8)) (.branch 64 (.leaf (-7)) (.leaf (-6)))),
  (.branch 60 (.leaf (-9)) (.branch 69 (.leaf (-8)) (.leaf (-4)))),
  (.branch 67 (.branch 65 (.leaf (-24)) (.branch 66 (.leaf (-20)) (.leaf (-16)))) (.branch 68 (.leaf (-12)) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 59 (.leaf (-2)) (.branch 60 (.leaf (-1)) (.leaf (0)))),
  (.branch 65 (.branch 63 (.branch 45 (.leaf (-17)) (.leaf (-16))) (.branch 64 (.leaf (-14)) (.leaf (-12)))) (.branch 67 (.branch 66 (.leaf (-10)) (.leaf (-8))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 61 (.branch 57 (.branch 55 (.branch 54 (.leaf (-22)) (.leaf (-21))) (.branch 56 (.leaf (-20)) (.leaf (-19)))) (.branch 59 (.branch 58 (.leaf (-18)) (.leaf (-17))) (.branch 60 (.leaf (-16)) (.leaf (-15))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (-14)) (.leaf (-13))) (.branch 64 (.leaf (-12)) (.leaf (-11)))) (.branch 67 (.branch 66 (.leaf (-10)) (.leaf (-9))) (.branch 68 (.leaf (-8)) (.branch 69 (.leaf (-7)) (.leaf (-6))))))),
  (.branch 68 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 69 (.leaf (-7)) (.leaf (-6))))]
def witnessP9_284_4695 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (6))) (.branch 11 (.leaf (4)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (1)) (.leaf (8))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (3)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (1))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (0)) (.leaf (3)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (7))) (.branch 29 (.leaf (4)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (2)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (4)) (.leaf (3)))) (.branch 41 (.branch 40 (.leaf (8)) (.leaf (2))) (.branch 42 (.leaf (0)) (.leaf (5))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (1)) (.leaf (6))) (.branch 46 (.leaf (4)) (.leaf (3)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (2))) (.branch 50 (.leaf (5)) (.branch 51 (.leaf (1)) (.leaf (7))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (6)) (.leaf (1))) (.branch 59 (.leaf (5)) (.branch 60 (.leaf (0)) (.leaf (3)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (2)) (.leaf (8))) (.branch 64 (.leaf (4)) (.leaf (1)))) (.branch 67 (.branch 66 (.leaf (0)) (.leaf (3))) (.branch 68 (.leaf (5)) (.branch 69 (.leaf (6)) (.leaf (2)))))))))
  code := certificateP9_4695
  counts := ![(.branch 31 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 65 (.leaf (9)) (.leaf (10)))))),
  (.branch 35 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 56 (.branch 41 (.leaf (5)) (.branch 49 (.leaf (6)) (.leaf (7)))) (.branch 62 (.leaf (8)) (.branch 70 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 39 (.leaf (5)) (.branch 47 (.leaf (6)) (.leaf (7)))) (.branch 61 (.leaf (8)) (.branch 67 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 69 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-29))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-23)) (.leaf (-26)))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (-1))) (.branch 50 (.leaf (-3)) (.leaf (-4)))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-55)) (.leaf (-56)))),
  (.branch 40 (.branch 17 (.leaf (0)) (.leaf (-19))) (.branch 63 (.leaf (-20)) (.leaf (-21))))]
  high := ![(.branch 55 (.branch 43 (.branch 37 (.leaf (-29)) (.leaf (-28))) (.branch 49 (.leaf (-27)) (.leaf (-26)))) (.branch 67 (.branch 61 (.leaf (-25)) (.leaf (-24))) (.branch 68 (.leaf (-18)) (.branch 69 (.leaf (-12)) (.leaf (-6)))))),
  (.branch 67 (.branch 66 (.leaf (-5)) (.leaf (-4))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.branch 63 (.leaf (-1)) (.leaf (0))),
  (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1)))),
  (.branch 66 (.branch 56 (.branch 47 (.leaf (-26)) (.leaf (-25))) (.branch 65 (.leaf (-24)) (.leaf (-20)))) (.branch 68 (.branch 67 (.leaf (-16)) (.leaf (-12))) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 69 (.leaf (-4)) (.leaf (-3))),
  (.branch 46 (.leaf (-5)) (.branch 58 (.leaf (-4)) (.leaf (-3)))),
  (.branch 60 (.branch 55 (.branch 53 (.branch 29 (.leaf (-56)) (.leaf (-54))) (.branch 54 (.leaf (-51)) (.leaf (-48)))) (.branch 57 (.branch 56 (.leaf (-45)) (.leaf (-42))) (.branch 58 (.leaf (-39)) (.branch 59 (.leaf (-36)) (.leaf (-33)))))) (.branch 65 (.branch 62 (.branch 61 (.leaf (-30)) (.leaf (-27))) (.branch 63 (.leaf (-24)) (.branch 64 (.leaf (-21)) (.leaf (-18))))) (.branch 67 (.branch 66 (.leaf (-15)) (.leaf (-12))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 66 (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-18)) (.leaf (-15)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-9))) (.branch 69 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_284_4696 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (7)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (3))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (1))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (8)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (4)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (5)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (6)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (3))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (7)) (.leaf (4)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (1)) (.leaf (5)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (3))) (.branch 42 (.leaf (8)) (.leaf (0))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (4)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (6)) (.leaf (3))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (5)) (.leaf (1))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (7)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (1)) (.branch 60 (.leaf (0)) (.leaf (4)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (5)) (.leaf (2))) (.branch 64 (.leaf (0)) (.leaf (6)))) (.branch 67 (.branch 66 (.leaf (1)) (.leaf (3))) (.branch 68 (.leaf (0)) (.branch 69 (.leaf (8)) (.leaf (4)))))))))
  code := certificateP9_4696
  counts := ![(.branch 33 (.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))) (.branch 50 (.branch 40 (.branch 36 (.leaf (10)) (.leaf (11))) (.branch 43 (.leaf (12)) (.branch 47 (.leaf (13)) (.leaf (14))))) (.branch 60 (.branch 54 (.leaf (15)) (.branch 57 (.leaf (16)) (.leaf (17)))) (.branch 64 (.leaf (18)) (.branch 68 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 38 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 67 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.branch 70 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4))))),
  (.branch 34 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 69 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 25 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.branch 28 (.leaf (-27)) (.leaf (-28)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-11)) (.leaf (-14)))),
  (.branch 26 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-23)) (.leaf (-24)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.branch 56 (.leaf (-19)) (.leaf (-22)))),
  (.branch 21 (.leaf (0)) (.branch 42 (.leaf (-5)) (.leaf (-10))))]
  high := ![(.branch 65 (.branch 61 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-2)))),
  (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1)))),
  (.branch 66 (.branch 64 (.leaf (-28)) (.branch 65 (.leaf (-24)) (.leaf (-20)))) (.branch 68 (.branch 67 (.leaf (-16)) (.leaf (-12))) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 59 (.branch 50 (.leaf (-14)) (.leaf (-13))) (.branch 68 (.leaf (-12)) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 62 (.leaf (-1)) (.leaf (0))),
  (.branch 66 (.branch 64 (.branch 63 (.leaf (-24)) (.leaf (-21))) (.branch 65 (.leaf (-18)) (.leaf (-15)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-9))) (.branch 69 (.leaf (-6)) (.leaf (-3))))),
  (.branch 67 (.branch 66 (.leaf (-10)) (.leaf (-8))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2))))),
  (.branch 63 (.branch 59 (.branch 57 (.leaf (-22)) (.branch 58 (.leaf (-21)) (.leaf (-20)))) (.branch 61 (.branch 60 (.leaf (-19)) (.leaf (-18))) (.branch 62 (.leaf (-17)) (.leaf (-16))))) (.branch 66 (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-14)) (.leaf (-13)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-11))) (.branch 69 (.leaf (-10)) (.leaf (-9)))))),
  (.branch 43 (.leaf (-10)) (.leaf (-9)))]
def witnessP9_284_4697 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (5))) (.branch 7 (.leaf (0)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (6))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (2)) (.leaf (8))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (3)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (0)) (.leaf (7)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (6))) (.branch 29 (.leaf (4)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (8)) (.leaf (5)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (4)) (.leaf (1)))) (.branch 41 (.branch 40 (.leaf (3)) (.leaf (6))) (.branch 42 (.leaf (0)) (.leaf (7))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (2)) (.leaf (1))) (.branch 46 (.leaf (4)) (.leaf (3)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (5))) (.branch 50 (.leaf (1)) (.branch 51 (.leaf (2)) (.leaf (8))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (6)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (2))) (.branch 59 (.leaf (3)) (.branch 60 (.leaf (0)) (.leaf (7)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (1)) (.leaf (5))) (.branch 64 (.leaf (4)) (.leaf (2)))) (.branch 67 (.branch 66 (.leaf (0)) (.leaf (3))) (.branch 68 (.leaf (1)) (.branch 69 (.leaf (8)) (.leaf (6)))))))))
  code := certificateP9_4697
  counts := ![(.branch 31 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 57 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 65 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 40 (.leaf (5)) (.branch 47 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 67 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 41 (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 56 (.leaf (3)) (.branch 70 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.branch 69 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-29))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 50 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))) (.branch 53 (.branch 24 (.leaf (-9)) (.leaf (-12))) (.branch 59 (.leaf (-14)) (.leaf (-17))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-23)) (.leaf (-26)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 41 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-19))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 55 (.branch 43 (.branch 37 (.leaf (-29)) (.leaf (-28))) (.branch 49 (.leaf (-27)) (.leaf (-26)))) (.branch 67 (.branch 61 (.leaf (-25)) (.leaf (-24))) (.branch 68 (.leaf (-18)) (.branch 69 (.leaf (-12)) (.leaf (-6)))))),
  (.branch 69 (.leaf (-4)) (.leaf (-3))),
  (.branch 67 (.branch 66 (.leaf (-5)) (.leaf (-4))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.branch 68 (.branch 60 (.leaf (-17)) (.leaf (-16))) (.branch 69 (.leaf (-14)) (.leaf (-12)))),
  (.branch 66 (.branch 56 (.branch 47 (.leaf (-26)) (.leaf (-25))) (.branch 65 (.leaf (-24)) (.leaf (-20)))) (.branch 68 (.branch 67 (.leaf (-16)) (.leaf (-12))) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 66 (.branch 64 (.branch 7 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 65 (.branch 62 (.branch 44 (.leaf (-19)) (.leaf (-18))) (.branch 63 (.leaf (-16)) (.branch 64 (.leaf (-14)) (.leaf (-12))))) (.branch 67 (.branch 66 (.leaf (-10)) (.leaf (-8))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (-2))]
def witnessP9_284_4698 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (5))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (6))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (2)) (.leaf (5))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (8)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (2))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (7)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (5))) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (6)) (.leaf (4))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (1)) (.leaf (8)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (5)) (.leaf (3)))) (.branch 41 (.branch 40 (.leaf (1)) (.leaf (4))) (.branch 42 (.leaf (0)) (.leaf (2))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (7)) (.leaf (1))) (.branch 46 (.leaf (5)) (.leaf (3)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (6))) (.branch 50 (.leaf (1)) (.branch 51 (.leaf (2)) (.leaf (4))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (8)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (5)) (.leaf (2))) (.branch 59 (.leaf (0)) (.branch 60 (.leaf (3)) (.leaf (7)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (1)) (.leaf (4))) (.branch 64 (.leaf (2)) (.leaf (0)))) (.branch 67 (.branch 66 (.leaf (6)) (.leaf (5))) (.branch 68 (.leaf (3)) (.branch 69 (.leaf (1)) (.leaf (8)))))))))
  code := certificateP9_4698
  counts := ![(.branch 30 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 40 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 69 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 55 (.branch 39 (.leaf (5)) (.branch 47 (.leaf (6)) (.leaf (7)))) (.branch 60 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.leaf (7))))),
  (.branch 38 (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 57 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 67 (.leaf (6)) (.leaf (7))))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 35 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.branch 70 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 24 (.leaf (-29)) (.leaf (-31)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.branch 50 (.leaf (-3)) (.leaf (-4))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 25 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 39 (.leaf (-10)) (.branch 60 (.leaf (-12)) (.leaf (-15))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-15))) (.branch 41 (.leaf (-20)) (.leaf (-23)))),
  (.branch 6 (.leaf (0)) (.branch 46 (.leaf (-9)) (.leaf (-13)))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0))]
  high := ![(.branch 67 (.branch 60 (.leaf (-31)) (.branch 66 (.leaf (-30)) (.leaf (-24)))) (.branch 68 (.leaf (-18)) (.branch 69 (.leaf (-12)) (.leaf (-6))))),
  (.branch 63 (.leaf (-4)) (.leaf (-3))),
  (.branch 67 (.branch 65 (.leaf (-6)) (.branch 66 (.leaf (-5)) (.leaf (-4)))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.branch 61 (.leaf (-15)) (.branch 69 (.leaf (-14)) (.leaf (-12)))),
  (.branch 65 (.branch 53 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 64 (.leaf (-21)) (.leaf (-19)))) (.branch 67 (.branch 66 (.leaf (-17)) (.leaf (-15))) (.branch 68 (.leaf (-13)) (.branch 69 (.leaf (-11)) (.leaf (-9)))))),
  (.branch 68 (.leaf (-13)) (.branch 69 (.leaf (-11)) (.leaf (-9)))),
  (.branch 68 (.branch 67 (.leaf (-8)) (.leaf (-6))) (.branch 69 (.leaf (-4)) (.leaf (-2)))),
  (.branch 65 (.branch 63 (.branch 62 (.leaf (-18)) (.leaf (-16))) (.branch 64 (.leaf (-14)) (.leaf (-12)))) (.branch 67 (.branch 66 (.leaf (-10)) (.leaf (-8))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (0))]
def witnessP9_284_4699 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (8)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (2)) (.leaf (3))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (6)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (8)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (3)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (4)) (.leaf (7))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 34 (.leaf (3)) (.leaf (1)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (4)) (.leaf (8)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (7))) (.branch 42 (.leaf (1)) (.leaf (3))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (5)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (6)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (0))) (.branch 50 (.leaf (4)) (.branch 51 (.leaf (2)) (.leaf (3))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (7)) (.leaf (5)))) (.branch 58 (.branch 57 (.leaf (8)) (.leaf (1))) (.branch 59 (.leaf (2)) (.branch 60 (.leaf (0)) (.leaf (3)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (4)) (.leaf (6))) (.branch 64 (.leaf (1)) (.leaf (0)))) (.branch 67 (.branch 66 (.leaf (2)) (.leaf (5))) (.branch 68 (.leaf (7)) (.branch 69 (.leaf (3)) (.leaf (1)))))))))
  code := certificateP9_4699
  counts := ![(.branch 30 (.branch 11 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 40 (.branch 36 (.leaf (7)) (.leaf (8))) (.branch 46 (.leaf (9)) (.leaf (10)))) (.branch 60 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 65 (.leaf (13)) (.leaf (14)))))),
  (.branch 35 (.branch 18 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))) (.branch 53 (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))) (.branch 64 (.branch 58 (.leaf (9)) (.leaf (10))) (.branch 70 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 34 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.branch 69 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 67 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 41 (.branch 12 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 55 (.leaf (3)) (.branch 68 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 19 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 14 (.leaf (-17)) (.leaf (-22)))) (.branch 49 (.branch 40 (.leaf (-23)) (.leaf (-24))) (.branch 54 (.leaf (-29)) (.leaf (-30))))),
  (.branch 23 (.leaf (0)) (.branch 58 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-26))),
  (.branch 9 (.leaf (0)) (.branch 32 (.leaf (-8)) (.leaf (-9)))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (-9))) (.branch 33 (.leaf (-10)) (.branch 47 (.leaf (-12)) (.leaf (-13))))),
  (.branch 41 (.branch 12 (.leaf (0)) (.leaf (-3))) (.branch 55 (.leaf (-4)) (.branch 68 (.leaf (-5)) (.leaf (-7))))),
  (.branch 4 (.leaf (0)) (.leaf (-27)))]
  high := ![(.branch 67 (.branch 55 (.leaf (-30)) (.branch 66 (.leaf (-29)) (.leaf (-26)))) (.branch 68 (.leaf (-23)) (.branch 69 (.leaf (-20)) (.leaf (-17))))),
  (.branch 65 (.leaf (-2)) (.branch 66 (.leaf (-1)) (.leaf (0)))),
  (.branch 67 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-4)),
  (.branch 65 (.branch 51 (.branch 39 (.leaf (-26)) (.leaf (-25))) (.branch 63 (.leaf (-24)) (.branch 64 (.leaf (-21)) (.leaf (-18))))) (.branch 67 (.branch 66 (.leaf (-15)) (.leaf (-12))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3)))),
  (.branch 66 (.branch 64 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 65 (.leaf (-11)) (.leaf (-10)))) (.branch 68 (.branch 67 (.leaf (-9)) (.leaf (-8))) (.branch 69 (.leaf (-7)) (.leaf (-6))))),
  (.branch 69 (.leaf (-7)) (.leaf (-6))),
  (.branch 63 (.branch 59 (.branch 40 (.leaf (-27)) (.branch 58 (.leaf (-26)) (.leaf (-24)))) (.branch 61 (.branch 60 (.leaf (-22)) (.leaf (-20))) (.branch 62 (.leaf (-18)) (.leaf (-16))))) (.branch 66 (.branch 64 (.leaf (-14)) (.branch 65 (.leaf (-12)) (.leaf (-10)))) (.branch 68 (.branch 67 (.leaf (-8)) (.leaf (-6))) (.branch 69 (.leaf (-4)) (.leaf (-2))))))]
def witnessP9_284_4700 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (2)) (.leaf (4))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (8)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (4)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (5)) (.leaf (3))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (7))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (1)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (5)) (.leaf (6)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (3))) (.branch 42 (.leaf (1)) (.leaf (4))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (8)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (3)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (0))) (.branch 50 (.leaf (5)) (.branch 51 (.leaf (2)) (.leaf (4))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (7)))) (.branch 58 (.branch 57 (.leaf (6)) (.leaf (1))) (.branch 59 (.leaf (2)) (.branch 60 (.leaf (0)) (.leaf (4)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (5)) (.leaf (3))) (.branch 64 (.leaf (1)) (.leaf (0)))) (.branch 67 (.branch 66 (.leaf (2)) (.leaf (8))) (.branch 68 (.leaf (3)) (.branch 69 (.leaf (4)) (.leaf (1)))))))))
  code := certificateP9_4700
  counts := ![(.branch 30 (.branch 11 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 40 (.branch 36 (.leaf (7)) (.leaf (8))) (.branch 46 (.leaf (9)) (.leaf (10)))) (.branch 60 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 65 (.leaf (13)) (.leaf (14)))))),
  (.branch 35 (.branch 18 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))) (.branch 53 (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))) (.branch 64 (.branch 58 (.leaf (9)) (.leaf (10))) (.branch 70 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 55 (.branch 41 (.leaf (5)) (.branch 47 (.leaf (6)) (.leaf (7)))) (.branch 63 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 34 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.branch 69 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 67 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 19 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 14 (.leaf (-17)) (.leaf (-22)))) (.branch 49 (.branch 40 (.leaf (-23)) (.leaf (-24))) (.branch 54 (.leaf (-29)) (.leaf (-30))))),
  (.branch 23 (.leaf (0)) (.branch 58 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 33 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-6)))) (.branch 47 (.leaf (-9)) (.branch 68 (.leaf (-11)) (.leaf (-14))))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-26))),
  (.branch 4 (.leaf (0)) (.leaf (-27))),
  (.branch 9 (.leaf (0)) (.branch 32 (.leaf (-43)) (.leaf (-44)))),
  (.branch 44 (.branch 21 (.leaf (0)) (.leaf (-7))) (.branch 67 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 67 (.branch 55 (.leaf (-30)) (.branch 66 (.leaf (-29)) (.leaf (-26)))) (.branch 68 (.leaf (-23)) (.branch 69 (.leaf (-20)) (.leaf (-17))))),
  (.branch 65 (.leaf (-2)) (.branch 66 (.leaf (-1)) (.leaf (0)))),
  (.branch 67 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.branch 69 (.leaf (-14)) (.leaf (-12))),
  (.leaf (-4)),
  (.branch 65 (.branch 51 (.branch 39 (.leaf (-26)) (.leaf (-25))) (.branch 63 (.leaf (-24)) (.branch 64 (.leaf (-21)) (.leaf (-18))))) (.branch 67 (.branch 66 (.leaf (-15)) (.leaf (-12))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 63 (.branch 59 (.branch 40 (.leaf (-27)) (.branch 58 (.leaf (-26)) (.leaf (-24)))) (.branch 61 (.branch 60 (.leaf (-22)) (.leaf (-20))) (.branch 62 (.leaf (-18)) (.leaf (-16))))) (.branch 66 (.branch 64 (.leaf (-14)) (.branch 65 (.leaf (-12)) (.leaf (-10)))) (.branch 68 (.branch 67 (.leaf (-8)) (.leaf (-6))) (.branch 69 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 62 (.branch 58 (.branch 33 (.leaf (-44)) (.branch 57 (.leaf (-42)) (.leaf (-39)))) (.branch 60 (.branch 59 (.leaf (-36)) (.leaf (-33))) (.branch 61 (.leaf (-30)) (.leaf (-27))))) (.branch 66 (.branch 64 (.branch 63 (.leaf (-24)) (.leaf (-21))) (.branch 65 (.leaf (-18)) (.leaf (-15)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-9))) (.branch 69 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3))))]
def witnessP9_284_4701 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (3))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (6)) (.leaf (2))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (8))) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (2))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (5)) (.leaf (3)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (4))) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (7)) (.leaf (3))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (6)) (.leaf (2)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (4)) (.leaf (1)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (5)) (.leaf (3))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (8)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (4)) (.leaf (3))) (.branch 50 (.leaf (1)) (.branch 51 (.leaf (6)) (.leaf (2))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (7))) (.branch 55 (.leaf (3)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (4)) (.leaf (2))) (.branch 59 (.leaf (0)) (.branch 60 (.leaf (5)) (.leaf (3)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (1)) (.leaf (4))) (.branch 64 (.leaf (2)) (.leaf (0)))) (.branch 67 (.branch 66 (.leaf (8)) (.leaf (3))) (.branch 68 (.leaf (1)) (.branch 69 (.leaf (6)) (.leaf (2)))))))))
  code := certificateP9_4701
  counts := ![(.branch 30 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 35 (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))) (.branch 52 (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))) (.branch 64 (.branch 58 (.leaf (9)) (.leaf (10))) (.branch 70 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 61 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 67 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.branch 69 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-29)) (.leaf (-34)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-23))),
  (.branch 28 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 63 (.leaf (-20)) (.leaf (-26)))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 16 (.leaf (0)) (.leaf (-3))),
  (.branch 31 (.branch 9 (.leaf (0)) (.leaf (-15))) (.branch 54 (.leaf (-17)) (.leaf (-18)))),
  (.branch 19 (.leaf (0)) (.branch 66 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 60 (.branch 48 (.branch 42 (.leaf (-34)) (.leaf (-33))) (.branch 54 (.leaf (-32)) (.leaf (-31)))) (.branch 67 (.branch 66 (.leaf (-30)) (.leaf (-24))) (.branch 68 (.leaf (-18)) (.branch 69 (.leaf (-12)) (.leaf (-6)))))),
  (.branch 57 (.branch 51 (.leaf (-15)) (.leaf (-14))) (.branch 63 (.leaf (-13)) (.branch 69 (.leaf (-12)) (.leaf (-6))))),
  (.branch 53 (.branch 41 (.leaf (-5)) (.branch 47 (.leaf (-4)) (.leaf (-3)))) (.branch 59 (.leaf (-2)) (.branch 65 (.leaf (-1)) (.leaf (0))))),
  (.branch 56 (.branch 44 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 50 (.leaf (-21)) (.leaf (-20)))) (.branch 68 (.branch 62 (.leaf (-19)) (.leaf (-18))) (.branch 69 (.leaf (-12)) (.leaf (-6))))),
  (.branch 66 (.branch 64 (.leaf (-26)) (.branch 65 (.leaf (-24)) (.leaf (-22)))) (.branch 68 (.branch 67 (.leaf (-20)) (.leaf (-18))) (.branch 69 (.leaf (-16)) (.leaf (-14))))),
  (.branch 64 (.branch 61 (.branch 43 (.leaf (-21)) (.leaf (-20))) (.branch 62 (.leaf (-18)) (.branch 63 (.leaf (-16)) (.leaf (-14))))) (.branch 67 (.branch 65 (.leaf (-12)) (.branch 66 (.leaf (-10)) (.leaf (-8)))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 52 (.leaf (-3)) (.leaf (-2))),
  (.branch 62 (.branch 58 (.branch 56 (.branch 55 (.leaf (-18)) (.leaf (-17))) (.branch 57 (.leaf (-16)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-14)) (.leaf (-13))) (.branch 61 (.leaf (-12)) (.leaf (-11))))) (.branch 66 (.branch 64 (.branch 63 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-7)))) (.branch 68 (.branch 67 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 68 (.branch 67 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3))))]
def witnessP9_284_4702 : CycleWitness 9 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (3))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (4)) (.leaf (2))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (8))) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (2))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (3)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (6))) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (7)) (.leaf (3))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (4)) (.leaf (2)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (5)) (.leaf (1)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (4)) (.leaf (3))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (8)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (6)) (.leaf (3))) (.branch 50 (.leaf (1)) (.branch 51 (.leaf (4)) (.leaf (2))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (7))) (.branch 55 (.leaf (3)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (5)) (.leaf (2))) (.branch 59 (.leaf (0)) (.branch 60 (.leaf (4)) (.leaf (3)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (1)) (.leaf (6))) (.branch 64 (.leaf (2)) (.leaf (0)))) (.branch 67 (.branch 66 (.leaf (8)) (.leaf (3))) (.branch 68 (.leaf (1)) (.branch 69 (.leaf (4)) (.leaf (2)))))))))
  code := certificateP9_4702
  counts := ![(.branch 30 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 35 (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))) (.branch 52 (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))) (.branch 64 (.branch 58 (.leaf (9)) (.leaf (10))) (.branch 70 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 61 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 67 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.branch 69 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-29)) (.leaf (-34)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-23))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.branch 38 (.leaf (-15)) (.leaf (-16)))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (-6))) (.branch 63 (.leaf (-10)) (.leaf (-13)))),
  (.branch 31 (.branch 9 (.leaf (0)) (.leaf (-15))) (.branch 54 (.leaf (-17)) (.leaf (-18)))),
  (.branch 19 (.leaf (0)) (.branch 66 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 60 (.branch 48 (.branch 42 (.leaf (-34)) (.leaf (-33))) (.branch 54 (.leaf (-32)) (.leaf (-31)))) (.branch 67 (.branch 66 (.leaf (-30)) (.leaf (-24))) (.branch 68 (.leaf (-18)) (.branch 69 (.leaf (-12)) (.leaf (-6)))))),
  (.branch 57 (.branch 51 (.leaf (-15)) (.leaf (-14))) (.branch 63 (.leaf (-13)) (.branch 69 (.leaf (-12)) (.leaf (-6))))),
  (.branch 53 (.branch 41 (.leaf (-5)) (.branch 47 (.leaf (-4)) (.leaf (-3)))) (.branch 59 (.leaf (-2)) (.branch 65 (.leaf (-1)) (.leaf (0))))),
  (.branch 56 (.branch 44 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 50 (.leaf (-21)) (.leaf (-20)))) (.branch 68 (.branch 62 (.leaf (-19)) (.leaf (-18))) (.branch 69 (.leaf (-12)) (.leaf (-6))))),
  (.branch 52 (.branch 43 (.leaf (-7)) (.leaf (-6))) (.branch 61 (.leaf (-5)) (.leaf (-4)))),
  (.branch 63 (.branch 59 (.branch 39 (.leaf (-16)) (.branch 58 (.leaf (-15)) (.leaf (-14)))) (.branch 61 (.branch 60 (.leaf (-13)) (.leaf (-12))) (.branch 62 (.leaf (-11)) (.leaf (-10))))) (.branch 66 (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7)))) (.branch 68 (.branch 67 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 66 (.branch 64 (.leaf (-13)) (.branch 65 (.leaf (-12)) (.leaf (-11)))) (.branch 68 (.branch 67 (.leaf (-10)) (.leaf (-9))) (.branch 69 (.leaf (-8)) (.leaf (-7))))),
  (.branch 62 (.branch 58 (.branch 56 (.branch 55 (.leaf (-18)) (.leaf (-17))) (.branch 57 (.leaf (-16)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-14)) (.leaf (-13))) (.branch 61 (.leaf (-12)) (.leaf (-11))))) (.branch 66 (.branch 64 (.branch 63 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-7)))) (.branch 68 (.branch 67 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 68 (.branch 67 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3))))]
def witnessP9_284_4703 : CycleWitness 9 where
  length := 69
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (5)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (6)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (4)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (1)) (.leaf (0)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (2)) (.leaf (1))) (.branch 37 (.leaf (0)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (5)) (.leaf (2))) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (7)) (.leaf (0))) (.branch 45 (.leaf (2)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 50 (.leaf (0)) (.leaf (4))))))) (.branch 60 (.branch 55 (.branch 53 (.branch 52 (.leaf (1)) (.leaf (2))) (.branch 54 (.leaf (0)) (.leaf (3)))) (.branch 57 (.branch 56 (.leaf (1)) (.leaf (0))) (.branch 58 (.leaf (2)) (.branch 59 (.leaf (1)) (.leaf (0)))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (1)) (.leaf (5))) (.branch 63 (.leaf (2)) (.leaf (0)))) (.branch 66 (.branch 65 (.leaf (1)) (.leaf (8))) (.branch 67 (.leaf (0)) (.branch 68 (.leaf (2)) (.leaf (1)))))))))
  code := certificateP9_4703
  counts := ![(.branch 34 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))) (.branch 50 (.branch 41 (.branch 37 (.leaf (11)) (.leaf (12))) (.branch 44 (.leaf (13)) (.branch 47 (.leaf (14)) (.leaf (15))))) (.branch 60 (.branch 54 (.leaf (16)) (.branch 57 (.leaf (17)) (.leaf (18)))) (.branch 64 (.leaf (19)) (.branch 67 (.leaf (20)) (.leaf (21))))))),
  (.branch 36 (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))) (.branch 52 (.branch 42 (.branch 38 (.leaf (11)) (.leaf (12))) (.branch 46 (.leaf (13)) (.branch 48 (.leaf (14)) (.leaf (15))))) (.branch 61 (.branch 56 (.leaf (16)) (.branch 59 (.leaf (17)) (.leaf (18)))) (.branch 65 (.leaf (19)) (.branch 69 (.leaf (20)) (.leaf (21))))))),
  (.branch 35 (.branch 17 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))) (.branch 53 (.branch 45 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 49 (.leaf (10)) (.leaf (11)))) (.branch 63 (.branch 58 (.leaf (12)) (.leaf (13))) (.branch 68 (.leaf (14)) (.leaf (15)))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1))),
  (.branch 66 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-16)) (.leaf (-18)))),
  (.branch 25 (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-5)))) (.branch 48 (.branch 38 (.leaf (-6)) (.leaf (-8))) (.branch 61 (.leaf (-9)) (.leaf (-11))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 30 (.leaf (-7)) (.branch 53 (.leaf (-8)) (.leaf (-9))))),
  (.branch 9 (.leaf (0)) (.leaf (-14))),
  (.branch 5 (.leaf (0)) (.leaf (-18))),
  (.branch 16 (.leaf (0)) (.leaf (-7))),
  (.branch 20 (.leaf (0)) (.leaf (-49))),
  (.branch 43 (.leaf (0)) (.leaf (-26))),
  (.branch 66 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 61 (.branch 51 (.leaf (-18)) (.leaf (-17))) (.branch 68 (.leaf (-14)) (.leaf (-7)))),
  (.branch 66 (.branch 62 (.leaf (-11)) (.leaf (-10))) (.branch 67 (.leaf (-8)) (.branch 68 (.leaf (-6)) (.leaf (-4))))),
  (.branch 59 (.branch 54 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-7)) (.leaf (-6)))),
  (.branch 62 (.branch 58 (.branch 56 (.leaf (-14)) (.branch 57 (.leaf (-13)) (.leaf (-12)))) (.branch 60 (.branch 59 (.leaf (-11)) (.leaf (-10))) (.branch 61 (.leaf (-9)) (.leaf (-8))))) (.branch 65 (.branch 63 (.leaf (-7)) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 67 (.branch 66 (.leaf (-4)) (.leaf (-3))) (.branch 68 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 60 (.branch 55 (.branch 53 (.branch 52 (.leaf (-18)) (.leaf (-17))) (.branch 54 (.leaf (-16)) (.leaf (-15)))) (.branch 57 (.branch 56 (.leaf (-14)) (.leaf (-13))) (.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-11)) (.leaf (-10)))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (-9)) (.leaf (-8))) (.branch 63 (.leaf (-7)) (.leaf (-6)))) (.branch 66 (.branch 65 (.leaf (-5)) (.leaf (-4))) (.branch 67 (.leaf (-3)) (.branch 68 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 65 (.branch 63 (.leaf (-7)) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 67 (.branch 66 (.leaf (-4)) (.leaf (-3))) (.branch 68 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.branch 32 (.branch 26 (.branch 23 (.branch 21 (.leaf (-49)) (.branch 22 (.leaf (-48)) (.leaf (-47)))) (.branch 24 (.leaf (-46)) (.branch 25 (.leaf (-45)) (.leaf (-44))))) (.branch 29 (.branch 27 (.leaf (-43)) (.branch 28 (.leaf (-42)) (.leaf (-41)))) (.branch 30 (.leaf (-40)) (.branch 31 (.leaf (-39)) (.leaf (-38)))))) (.branch 38 (.branch 35 (.branch 33 (.leaf (-37)) (.branch 34 (.leaf (-36)) (.leaf (-35)))) (.branch 36 (.leaf (-34)) (.branch 37 (.leaf (-33)) (.leaf (-32))))) (.branch 41 (.branch 39 (.leaf (-31)) (.branch 40 (.leaf (-30)) (.leaf (-29)))) (.branch 42 (.leaf (-28)) (.branch 43 (.leaf (-27)) (.leaf (-26))))))) (.branch 56 (.branch 50 (.branch 47 (.branch 45 (.leaf (-25)) (.branch 46 (.leaf (-24)) (.leaf (-23)))) (.branch 48 (.leaf (-22)) (.branch 49 (.leaf (-21)) (.leaf (-20))))) (.branch 53 (.branch 51 (.leaf (-19)) (.branch 52 (.leaf (-18)) (.leaf (-17)))) (.branch 54 (.leaf (-16)) (.branch 55 (.leaf (-15)) (.leaf (-14)))))) (.branch 62 (.branch 59 (.branch 57 (.leaf (-13)) (.branch 58 (.leaf (-12)) (.leaf (-11)))) (.branch 60 (.leaf (-10)) (.branch 61 (.leaf (-9)) (.leaf (-8))))) (.branch 65 (.branch 63 (.leaf (-7)) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 67 (.branch 66 (.leaf (-4)) (.leaf (-3))) (.branch 68 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 56 (.branch 49 (.branch 46 (.branch 44 (.leaf (-26)) (.branch 45 (.leaf (-25)) (.leaf (-24)))) (.branch 47 (.leaf (-23)) (.branch 48 (.leaf (-22)) (.leaf (-21))))) (.branch 52 (.branch 50 (.leaf (-20)) (.branch 51 (.leaf (-19)) (.leaf (-18)))) (.branch 54 (.branch 53 (.leaf (-17)) (.leaf (-16))) (.branch 55 (.leaf (-15)) (.leaf (-14)))))) (.branch 62 (.branch 59 (.branch 57 (.leaf (-13)) (.branch 58 (.leaf (-12)) (.leaf (-11)))) (.branch 60 (.leaf (-10)) (.branch 61 (.leaf (-9)) (.leaf (-8))))) (.branch 65 (.branch 63 (.leaf (-7)) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 67 (.branch 66 (.leaf (-4)) (.leaf (-3))) (.branch 68 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 67 (.leaf (-3)) (.branch 68 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_284_4704 : CycleWitness 9 where
  length := 69
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (8)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (2))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (3))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (7))) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (6))) (.branch 28 (.leaf (0)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (8)) (.leaf (0))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (2)) (.leaf (1)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (5))) (.branch 37 (.leaf (3)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (6))) (.branch 41 (.leaf (2)) (.leaf (7))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (4)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 50 (.leaf (5)) (.leaf (0))))))) (.branch 60 (.branch 55 (.branch 53 (.branch 52 (.leaf (1)) (.leaf (8))) (.branch 54 (.leaf (0)) (.leaf (6)))) (.branch 57 (.branch 56 (.leaf (2)) (.leaf (1))) (.branch 58 (.leaf (0)) (.branch 59 (.leaf (4)) (.leaf (3)))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (5)) (.leaf (2)))) (.branch 66 (.branch 65 (.leaf (7)) (.leaf (0))) (.branch 67 (.leaf (1)) (.branch 68 (.leaf (6)) (.leaf (3)))))))))
  code := certificateP9_4704
  counts := ![(.branch 31 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 51 (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.branch 47 (.leaf (12)) (.leaf (13))))) (.branch 58 (.branch 54 (.leaf (14)) (.leaf (15))) (.branch 62 (.leaf (16)) (.branch 66 (.leaf (17)) (.leaf (18))))))),
  (.branch 34 (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 52 (.branch 44 (.branch 38 (.leaf (8)) (.leaf (9))) (.branch 48 (.leaf (10)) (.leaf (11)))) (.branch 61 (.branch 57 (.leaf (12)) (.leaf (13))) (.branch 67 (.leaf (14)) (.leaf (15)))))),
  (.branch 33 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 41 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 37 (.branch 14 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 60 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 69 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 40 (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 55 (.leaf (3)) (.branch 68 (.leaf (4)) (.leaf (5))))),
  (.branch 42 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-17)) (.leaf (-21)))),
  (.branch 29 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 15 (.leaf (-4)) (.leaf (-5)))) (.branch 52 (.branch 38 (.leaf (-6)) (.leaf (-7))) (.branch 61 (.leaf (-8)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-14)) (.leaf (-16)))),
  (.branch 23 (.leaf (0)) (.branch 46 (.leaf (-3)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-10)) (.leaf (-11)))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (-5))) (.branch 63 (.leaf (-6)) (.leaf (-7)))),
  (.branch 13 (.leaf (0)) (.branch 40 (.leaf (-1)) (.leaf (-2)))),
  (.branch 19 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 63 (.branch 55 (.leaf (-21)) (.branch 59 (.leaf (-20)) (.leaf (-19)))) (.branch 67 (.leaf (-18)) (.branch 68 (.leaf (-12)) (.leaf (-6))))),
  (.branch 62 (.leaf (-9)) (.branch 68 (.leaf (-8)) (.leaf (-7)))),
  (.branch 66 (.branch 57 (.leaf (-16)) (.branch 65 (.leaf (-15)) (.leaf (-12)))) (.branch 67 (.leaf (-9)) (.branch 68 (.leaf (-6)) (.leaf (-3))))),
  (.branch 62 (.branch 47 (.leaf (-6)) (.branch 61 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.branch 63 (.leaf (-3)) (.leaf (-2))) (.branch 65 (.leaf (-1)) (.leaf (0))))),
  (.branch 64 (.branch 61 (.branch 60 (.leaf (-11)) (.leaf (-10))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-8)) (.leaf (-7))))) (.branch 66 (.branch 65 (.leaf (-6)) (.leaf (-5))) (.branch 67 (.leaf (-4)) (.branch 68 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 66 (.branch 64 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 67 (.leaf (-4)) (.branch 68 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 67 (.branch 66 (.leaf (-4)) (.leaf (-3))) (.branch 68 (.leaf (-2)) (.leaf (-1)))),
  (.branch 61 (.branch 57 (.branch 55 (.branch 54 (.leaf (-16)) (.leaf (-15))) (.branch 56 (.leaf (-14)) (.leaf (-13)))) (.branch 59 (.branch 58 (.leaf (-12)) (.leaf (-11))) (.branch 60 (.leaf (-10)) (.leaf (-9))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (-8)) (.leaf (-7))) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 67 (.branch 66 (.leaf (-4)) (.leaf (-3))) (.branch 68 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_284_4705 : CycleWitness 9 where
  length := 69
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (0))) (.branch 7 (.leaf (6)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (3))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (7)) (.leaf (5))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (1)) (.leaf (0))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (8)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (4))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (5))) (.branch 28 (.leaf (0)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (7))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (6)) (.leaf (2)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (4)) (.leaf (0))) (.branch 37 (.leaf (1)) (.leaf (8)))) (.branch 40 (.branch 39 (.leaf (3)) (.leaf (0))) (.branch 41 (.leaf (5)) (.leaf (2))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (4)) (.leaf (6)))) (.branch 48 (.branch 47 (.leaf (7)) (.leaf (0))) (.branch 49 (.leaf (3)) (.branch 50 (.leaf (2)) (.leaf (1))))))) (.branch 60 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (8)) (.leaf (1))) (.branch 58 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (0)))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (6)) (.leaf (4))) (.branch 63 (.leaf (0)) (.leaf (1)))) (.branch 66 (.branch 65 (.leaf (7)) (.leaf (2))) (.branch 67 (.leaf (0)) (.branch 68 (.leaf (5)) (.leaf (3)))))))))
  code := certificateP9_4705
  counts := ![(.branch 32 (.branch 12 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 52 (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.branch 48 (.leaf (12)) (.leaf (13))))) (.branch 60 (.branch 55 (.leaf (14)) (.leaf (15))) (.branch 63 (.leaf (16)) (.branch 67 (.leaf (17)) (.leaf (18))))))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 34 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 66 (.leaf (8)) (.leaf (9)))))),
  (.branch 39 (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 59 (.branch 49 (.leaf (4)) (.leaf (5))) (.branch 69 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.leaf (7))))),
  (.branch 41 (.branch 14 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 54 (.leaf (3)) (.branch 68 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 61 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 43 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 57 (.leaf (-49)) (.leaf (-51)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-29)) (.leaf (-33)))),
  (.branch 19 (.leaf (0)) (.leaf (-5))),
  (.branch 45 (.branch 4 (.leaf (0)) (.branch 35 (.leaf (-13)) (.leaf (-14)))) (.branch 53 (.leaf (-15)) (.branch 62 (.leaf (-20)) (.leaf (-23))))),
  (.branch 27 (.leaf (0)) (.branch 54 (.leaf (-1)) (.leaf (-2)))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (-15))) (.branch 33 (.leaf (-16)) (.branch 46 (.leaf (-21)) (.leaf (-24))))),
  (.branch 13 (.leaf (0)) (.branch 47 (.leaf (-13)) (.leaf (-15)))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (-25))) (.branch 38 (.leaf (-26)) (.leaf (-29))))]
  high := ![(.branch 68 (.leaf (-5)) (.leaf (-4))),
  (.branch 66 (.branch 58 (.leaf (-51)) (.branch 65 (.leaf (-50)) (.leaf (-40)))) (.branch 67 (.leaf (-30)) (.branch 68 (.leaf (-20)) (.leaf (-10))))),
  (.branch 43 (.branch 27 (.branch 19 (.leaf (-33)) (.leaf (-32))) (.branch 35 (.leaf (-31)) (.leaf (-30)))) (.branch 59 (.branch 51 (.leaf (-29)) (.leaf (-28))) (.branch 67 (.leaf (-27)) (.branch 68 (.leaf (-21)) (.leaf (-15)))))),
  (.branch 40 (.branch 20 (.leaf (-5)) (.branch 30 (.leaf (-4)) (.leaf (-3)))) (.branch 50 (.leaf (-2)) (.branch 60 (.leaf (-1)) (.leaf (0))))),
  (.branch 65 (.branch 63 (.leaf (-23)) (.branch 64 (.leaf (-21)) (.leaf (-19)))) (.branch 67 (.branch 66 (.leaf (-17)) (.leaf (-15))) (.branch 68 (.leaf (-13)) (.leaf (-11))))),
  (.leaf (-2)),
  (.branch 64 (.branch 62 (.branch 47 (.leaf (-24)) (.leaf (-23))) (.branch 63 (.leaf (-21)) (.leaf (-19)))) (.branch 66 (.branch 65 (.leaf (-17)) (.leaf (-15))) (.branch 67 (.leaf (-13)) (.branch 68 (.leaf (-11)) (.leaf (-9)))))),
  (.branch 66 (.branch 48 (.leaf (-15)) (.leaf (-13))) (.branch 67 (.leaf (-10)) (.branch 68 (.leaf (-7)) (.leaf (-4))))),
  (.branch 62 (.branch 58 (.branch 39 (.leaf (-29)) (.branch 57 (.leaf (-28)) (.leaf (-26)))) (.branch 60 (.branch 59 (.leaf (-24)) (.leaf (-22))) (.branch 61 (.leaf (-20)) (.leaf (-18))))) (.branch 65 (.branch 63 (.leaf (-16)) (.branch 64 (.leaf (-14)) (.leaf (-12)))) (.branch 67 (.branch 66 (.leaf (-10)) (.leaf (-8))) (.branch 68 (.leaf (-6)) (.leaf (-4))))))]
def witnessP9_284_4706 : CycleWitness 9 where
  length := 69
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (2)) (.leaf (0))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (5)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (7)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (0)) (.leaf (2)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (5)) (.leaf (1))) (.branch 37 (.leaf (0)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (4)) (.leaf (1))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (6))) (.branch 45 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (4)) (.branch 50 (.leaf (0)) (.leaf (2))))))) (.branch 60 (.branch 55 (.branch 53 (.branch 52 (.leaf (5)) (.leaf (0))) (.branch 54 (.leaf (1)) (.leaf (3)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (2))) (.branch 58 (.leaf (4)) (.branch 59 (.leaf (1)) (.leaf (0)))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (8)) (.leaf (2))) (.branch 63 (.leaf (0)) (.leaf (3)))) (.branch 66 (.branch 65 (.leaf (1)) (.leaf (0))) (.branch 67 (.leaf (4)) (.branch 68 (.leaf (2)) (.leaf (5)))))))))
  code := certificateP9_4706
  counts := ![(.branch 33 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))) (.branch 50 (.branch 40 (.branch 37 (.leaf (11)) (.leaf (12))) (.branch 43 (.leaf (13)) (.branch 47 (.leaf (14)) (.leaf (15))))) (.branch 60 (.branch 53 (.leaf (16)) (.branch 56 (.leaf (17)) (.leaf (18)))) (.branch 63 (.leaf (19)) (.branch 66 (.leaf (20)) (.leaf (21))))))),
  (.branch 31 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 57 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 67 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.branch 69 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 61 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 7 (.leaf (-18)) (.branch 10 (.leaf (-20)) (.leaf (-22))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-15)) (.leaf (-17)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 46 (.leaf (-45)) (.leaf (-46)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-21)) (.leaf (-23)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-51))),
  (.branch 26 (.leaf (0)) (.leaf (-43))),
  (.branch 61 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 67 (.branch 57 (.leaf (-22)) (.leaf (-21))) (.branch 68 (.leaf (-14)) (.leaf (-7)))),
  (.branch 66 (.branch 60 (.leaf (-17)) (.leaf (-16))) (.branch 67 (.leaf (-12)) (.branch 68 (.leaf (-8)) (.leaf (-4))))),
  (.branch 63 (.leaf (-5)) (.leaf (-4))),
  (.branch 65 (.branch 47 (.leaf (-46)) (.branch 56 (.leaf (-43)) (.leaf (-40)))) (.branch 67 (.branch 66 (.leaf (-32)) (.leaf (-24))) (.branch 68 (.leaf (-16)) (.leaf (-8))))),
  (.branch 50 (.branch 24 (.leaf (-23)) (.leaf (-22))) (.branch 59 (.leaf (-19)) (.branch 68 (.leaf (-16)) (.leaf (-8))))),
  (.leaf (0)),
  (.branch 56 (.branch 49 (.branch 46 (.branch 10 (.leaf (-51)) (.branch 45 (.leaf (-50)) (.leaf (-48)))) (.branch 47 (.leaf (-46)) (.branch 48 (.leaf (-44)) (.leaf (-42))))) (.branch 52 (.branch 50 (.leaf (-40)) (.branch 51 (.leaf (-38)) (.leaf (-36)))) (.branch 54 (.branch 53 (.leaf (-34)) (.leaf (-32))) (.branch 55 (.leaf (-30)) (.leaf (-28)))))) (.branch 62 (.branch 59 (.branch 57 (.leaf (-26)) (.branch 58 (.leaf (-24)) (.leaf (-22)))) (.branch 60 (.leaf (-20)) (.branch 61 (.leaf (-18)) (.leaf (-16))))) (.branch 65 (.branch 63 (.leaf (-14)) (.branch 64 (.leaf (-12)) (.leaf (-10)))) (.branch 67 (.branch 66 (.leaf (-8)) (.leaf (-6))) (.branch 68 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 47 (.branch 36 (.branch 31 (.branch 28 (.branch 27 (.leaf (-43)) (.leaf (-42))) (.branch 29 (.leaf (-41)) (.branch 30 (.leaf (-40)) (.leaf (-39))))) (.branch 33 (.branch 32 (.leaf (-38)) (.leaf (-37))) (.branch 34 (.leaf (-36)) (.branch 35 (.leaf (-35)) (.leaf (-34)))))) (.branch 41 (.branch 38 (.branch 37 (.leaf (-33)) (.leaf (-32))) (.branch 39 (.leaf (-31)) (.branch 40 (.leaf (-30)) (.leaf (-29))))) (.branch 44 (.branch 42 (.leaf (-28)) (.branch 43 (.leaf (-27)) (.leaf (-26)))) (.branch 45 (.leaf (-25)) (.branch 46 (.leaf (-24)) (.leaf (-23))))))) (.branch 58 (.branch 52 (.branch 49 (.branch 48 (.leaf (-22)) (.leaf (-21))) (.branch 50 (.leaf (-20)) (.branch 51 (.leaf (-19)) (.leaf (-18))))) (.branch 55 (.branch 53 (.leaf (-17)) (.branch 54 (.leaf (-16)) (.leaf (-15)))) (.branch 56 (.leaf (-14)) (.branch 57 (.leaf (-13)) (.leaf (-12)))))) (.branch 63 (.branch 60 (.branch 59 (.leaf (-11)) (.leaf (-10))) (.branch 61 (.leaf (-9)) (.branch 62 (.leaf (-8)) (.leaf (-7))))) (.branch 66 (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-5)) (.leaf (-4)))) (.branch 67 (.leaf (-3)) (.branch 68 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 65 (.branch 63 (.branch 62 (.leaf (-8)) (.leaf (-7))) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 67 (.branch 66 (.leaf (-4)) (.leaf (-3))) (.branch 68 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_284_4707 : CycleWitness 9 where
  length := 69
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (2)) (.leaf (0))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (6)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (0)) (.leaf (2)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (8)) (.leaf (1))) (.branch 37 (.leaf (0)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (4)) (.leaf (1))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (6))) (.branch 45 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (5)) (.branch 50 (.leaf (0)) (.leaf (2))))))) (.branch 60 (.branch 55 (.branch 53 (.branch 52 (.leaf (7)) (.leaf (0))) (.branch 54 (.leaf (1)) (.leaf (3)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (2))) (.branch 58 (.leaf (4)) (.branch 59 (.leaf (1)) (.leaf (0)))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (6)) (.leaf (2))) (.branch 63 (.leaf (0)) (.leaf (3)))) (.branch 66 (.branch 65 (.leaf (1)) (.leaf (0))) (.branch 67 (.leaf (5)) (.branch 68 (.leaf (2)) (.leaf (8)))))))))
  code := certificateP9_4707
  counts := ![(.branch 33 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))) (.branch 50 (.branch 40 (.branch 37 (.leaf (11)) (.leaf (12))) (.branch 43 (.leaf (13)) (.branch 47 (.leaf (14)) (.leaf (15))))) (.branch 60 (.branch 53 (.leaf (16)) (.branch 56 (.leaf (17)) (.leaf (18)))) (.branch 63 (.leaf (19)) (.branch 66 (.leaf (20)) (.leaf (21))))))),
  (.branch 31 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 57 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 67 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 35 (.leaf (0)) (.branch 69 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 7 (.leaf (-18)) (.branch 10 (.leaf (-20)) (.leaf (-22))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-15)) (.leaf (-17)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 46 (.leaf (-45)) (.leaf (-46)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-45)) (.leaf (-46)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (-9))) (.branch 49 (.leaf (-10)) (.leaf (-11)))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (-33)) (.leaf (-34)))),
  (.branch 18 (.leaf (0)) (.branch 52 (.leaf (-33)) (.leaf (-34)))),
  (.leaf (0))]
  high := ![(.branch 67 (.branch 57 (.leaf (-22)) (.leaf (-21))) (.branch 68 (.leaf (-14)) (.leaf (-7)))),
  (.branch 66 (.branch 60 (.leaf (-17)) (.leaf (-16))) (.branch 67 (.leaf (-12)) (.branch 68 (.leaf (-8)) (.leaf (-4))))),
  (.branch 63 (.leaf (-5)) (.leaf (-4))),
  (.branch 65 (.branch 47 (.leaf (-46)) (.branch 56 (.leaf (-43)) (.leaf (-40)))) (.branch 67 (.branch 66 (.leaf (-32)) (.leaf (-24))) (.branch 68 (.leaf (-16)) (.leaf (-8))))),
  (.branch 63 (.branch 60 (.branch 24 (.leaf (-46)) (.branch 59 (.leaf (-44)) (.leaf (-40)))) (.branch 61 (.leaf (-36)) (.branch 62 (.leaf (-32)) (.leaf (-28))))) (.branch 66 (.branch 64 (.leaf (-24)) (.branch 65 (.leaf (-20)) (.leaf (-16)))) (.branch 67 (.leaf (-12)) (.branch 68 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 50 (.leaf (-11)) (.branch 68 (.leaf (-8)) (.leaf (-4)))),
  (.branch 64 (.branch 62 (.branch 27 (.leaf (-34)) (.leaf (-32))) (.branch 63 (.leaf (-28)) (.leaf (-24)))) (.branch 66 (.branch 65 (.leaf (-20)) (.leaf (-16))) (.branch 67 (.leaf (-12)) (.branch 68 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 60 (.branch 56 (.branch 54 (.branch 53 (.leaf (-34)) (.leaf (-32))) (.branch 55 (.leaf (-30)) (.leaf (-28)))) (.branch 58 (.branch 57 (.leaf (-26)) (.leaf (-24))) (.branch 59 (.leaf (-22)) (.leaf (-20))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (-18)) (.leaf (-16))) (.branch 63 (.leaf (-14)) (.leaf (-12)))) (.branch 66 (.branch 65 (.leaf (-10)) (.leaf (-8))) (.branch 67 (.leaf (-6)) (.branch 68 (.leaf (-4)) (.leaf (-2))))))),
  (.leaf (0))]
def witnessP9_284_4708 : CycleWitness 9 where
  length := 69
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (4))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (6)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (2))) (.branch 28 (.leaf (0)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (4))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (3)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (4)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (7)) (.leaf (3))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (2))) (.branch 45 (.leaf (1)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (3)) (.branch 50 (.leaf (2)) (.leaf (0))))))) (.branch 60 (.branch 55 (.branch 53 (.branch 52 (.leaf (5)) (.leaf (1))) (.branch 54 (.leaf (4)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (2)) (.leaf (3))) (.branch 58 (.leaf (1)) (.branch 59 (.leaf (0)) (.leaf (4)))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (2)) (.leaf (0))) (.branch 63 (.leaf (1)) (.leaf (8)))) (.branch 66 (.branch 65 (.leaf (3)) (.leaf (0))) (.branch 67 (.leaf (2)) (.branch 68 (.leaf (1)) (.leaf (4)))))))))
  code := certificateP9_4708
  counts := ![(.branch 32 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 51 (.branch 39 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.branch 47 (.leaf (12)) (.leaf (13))))) (.branch 59 (.branch 55 (.leaf (14)) (.leaf (15))) (.branch 62 (.leaf (16)) (.branch 66 (.leaf (17)) (.leaf (18))))))),
  (.branch 35 (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))) (.branch 53 (.branch 45 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 48 (.leaf (10)) (.leaf (11)))) (.branch 63 (.branch 58 (.leaf (12)) (.leaf (13))) (.branch 68 (.leaf (14)) (.leaf (15)))))),
  (.branch 33 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 61 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 67 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 37 (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 46 (.leaf (5)) (.leaf (6))) (.branch 60 (.leaf (7)) (.branch 69 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1))),
  (.branch 64 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-19)))),
  (.branch 25 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 48 (.leaf (-14)) (.leaf (-17)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 37 (.branch 14 (.leaf (0)) (.leaf (-2))) (.branch 60 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-17))),
  (.branch 18 (.leaf (0)) (.leaf (-51))),
  (.branch 41 (.leaf (0)) (.leaf (-28))),
  (.branch 64 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 67 (.branch 63 (.leaf (-19)) (.leaf (-18))) (.branch 68 (.leaf (-12)) (.leaf (-6)))),
  (.branch 54 (.branch 49 (.leaf (-17)) (.leaf (-16))) (.branch 59 (.leaf (-15)) (.branch 64 (.leaf (-14)) (.leaf (-13))))),
  (.branch 62 (.leaf (-9)) (.branch 68 (.leaf (-8)) (.leaf (-4)))),
  (.branch 66 (.branch 50 (.leaf (-14)) (.branch 58 (.leaf (-13)) (.leaf (-12)))) (.branch 67 (.leaf (-9)) (.branch 68 (.leaf (-6)) (.leaf (-3))))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.branch 64 (.leaf (-1)) (.leaf (0))))),
  (.branch 60 (.branch 56 (.branch 54 (.branch 53 (.leaf (-17)) (.leaf (-16))) (.branch 55 (.leaf (-15)) (.leaf (-14)))) (.branch 58 (.branch 57 (.leaf (-13)) (.leaf (-12))) (.branch 59 (.leaf (-11)) (.leaf (-10))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (-9)) (.leaf (-8))) (.branch 63 (.leaf (-7)) (.leaf (-6)))) (.branch 66 (.branch 65 (.leaf (-5)) (.leaf (-4))) (.branch 67 (.leaf (-3)) (.branch 68 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 30 (.branch 24 (.branch 21 (.branch 19 (.leaf (-51)) (.branch 20 (.leaf (-50)) (.leaf (-49)))) (.branch 22 (.leaf (-48)) (.branch 23 (.leaf (-47)) (.leaf (-46))))) (.branch 27 (.branch 25 (.leaf (-45)) (.branch 26 (.leaf (-44)) (.leaf (-43)))) (.branch 28 (.leaf (-42)) (.branch 29 (.leaf (-41)) (.leaf (-40)))))) (.branch 36 (.branch 33 (.branch 31 (.leaf (-39)) (.branch 32 (.leaf (-38)) (.leaf (-37)))) (.branch 34 (.leaf (-36)) (.branch 35 (.leaf (-35)) (.leaf (-34))))) (.branch 39 (.branch 37 (.leaf (-33)) (.branch 38 (.leaf (-32)) (.leaf (-31)))) (.branch 41 (.branch 40 (.leaf (-30)) (.leaf (-29))) (.branch 42 (.leaf (-28)) (.leaf (-27))))))) (.branch 56 (.branch 49 (.branch 46 (.branch 44 (.leaf (-26)) (.branch 45 (.leaf (-25)) (.leaf (-24)))) (.branch 47 (.leaf (-23)) (.branch 48 (.leaf (-22)) (.leaf (-21))))) (.branch 52 (.branch 50 (.leaf (-20)) (.branch 51 (.leaf (-19)) (.leaf (-18)))) (.branch 54 (.branch 53 (.leaf (-17)) (.leaf (-16))) (.branch 55 (.leaf (-15)) (.leaf (-14)))))) (.branch 62 (.branch 59 (.branch 57 (.leaf (-13)) (.branch 58 (.leaf (-12)) (.leaf (-11)))) (.branch 60 (.leaf (-10)) (.branch 61 (.leaf (-9)) (.leaf (-8))))) (.branch 65 (.branch 63 (.leaf (-7)) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 67 (.branch 66 (.leaf (-4)) (.leaf (-3))) (.branch 68 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 55 (.branch 48 (.branch 44 (.branch 42 (.leaf (-28)) (.branch 43 (.leaf (-27)) (.leaf (-26)))) (.branch 46 (.branch 45 (.leaf (-25)) (.leaf (-24))) (.branch 47 (.leaf (-23)) (.leaf (-22))))) (.branch 51 (.branch 49 (.leaf (-21)) (.branch 50 (.leaf (-20)) (.leaf (-19)))) (.branch 53 (.branch 52 (.leaf (-18)) (.leaf (-17))) (.branch 54 (.leaf (-16)) (.leaf (-15)))))) (.branch 62 (.branch 58 (.branch 56 (.leaf (-14)) (.branch 57 (.leaf (-13)) (.leaf (-12)))) (.branch 60 (.branch 59 (.leaf (-11)) (.leaf (-10))) (.branch 61 (.leaf (-9)) (.leaf (-8))))) (.branch 65 (.branch 63 (.leaf (-7)) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 67 (.branch 66 (.leaf (-4)) (.leaf (-3))) (.branch 68 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 66 (.branch 65 (.leaf (-5)) (.leaf (-4))) (.branch 67 (.leaf (-3)) (.branch 68 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_284_4709 : CycleWitness 9 where
  length := 69
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (4))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (8)) (.leaf (5))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (6))) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (5)) (.leaf (7))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (6))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (1)) (.leaf (0)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (5)) (.leaf (2))) (.branch 37 (.leaf (3)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (8)) (.leaf (4))) (.branch 41 (.leaf (1)) (.leaf (6))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (5)) (.leaf (0))) (.branch 45 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (4)) (.branch 50 (.leaf (7)) (.leaf (2))))))) (.branch 60 (.branch 55 (.branch 53 (.branch 52 (.leaf (5)) (.leaf (0))) (.branch 54 (.leaf (6)) (.leaf (3)))) (.branch 57 (.branch 56 (.leaf (1)) (.leaf (0))) (.branch 58 (.leaf (4)) (.branch 59 (.leaf (2)) (.leaf (5)))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (0)) (.leaf (8))) (.branch 63 (.leaf (3)) (.leaf (1)))) (.branch 66 (.branch 65 (.leaf (6)) (.leaf (4))) (.branch 67 (.leaf (0)) (.branch 68 (.leaf (2)) (.leaf (5)))))))))
  code := certificateP9_4709
  counts := ![(.branch 34 (.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))) (.branch 53 (.branch 44 (.branch 38 (.leaf (8)) (.leaf (9))) (.branch 47 (.leaf (10)) (.leaf (11)))) (.branch 61 (.branch 57 (.leaf (12)) (.leaf (13))) (.branch 67 (.leaf (14)) (.leaf (15)))))),
  (.branch 33 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 41 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 45 (.leaf (5)) (.leaf (6))) (.branch 59 (.leaf (7)) (.branch 68 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.branch 69 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 24 (.branch 1 (.leaf (0)) (.branch 15 (.leaf (-4)) (.leaf (-5)))) (.branch 47 (.branch 38 (.leaf (-6)) (.leaf (-7))) (.branch 61 (.leaf (-8)) (.leaf (-9))))),
  (.branch 2 (.leaf (0)) (.leaf (-17))),
  (.branch 28 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 51 (.leaf (-4)) (.leaf (-5)))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (-45))) (.branch 37 (.leaf (-47)) (.leaf (-49)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-21)) (.leaf (-26)))),
  (.branch 17 (.leaf (0)) (.branch 60 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 16 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 62 (.leaf (-9)) (.branch 68 (.leaf (-8)) (.leaf (-7)))),
  (.branch 65 (.branch 49 (.leaf (-17)) (.branch 57 (.leaf (-16)) (.leaf (-15)))) (.branch 67 (.branch 66 (.leaf (-12)) (.leaf (-9))) (.branch 68 (.leaf (-6)) (.leaf (-3))))),
  (.branch 60 (.leaf (-5)) (.leaf (-4))),
  (.branch 65 (.branch 38 (.leaf (-49)) (.branch 64 (.leaf (-48)) (.leaf (-40)))) (.branch 67 (.branch 66 (.leaf (-32)) (.leaf (-24))) (.branch 68 (.leaf (-16)) (.leaf (-8))))),
  (.branch 41 (.branch 15 (.leaf (-26)) (.leaf (-25))) (.branch 67 (.leaf (-24)) (.branch 68 (.leaf (-16)) (.leaf (-8))))),
  (.branch 61 (.leaf (-3)) (.leaf (0))),
  (.branch 67 (.branch 66 (.leaf (-8)) (.leaf (-6))) (.branch 68 (.leaf (-4)) (.leaf (-2)))),
  (.branch 59 (.branch 54 (.branch 52 (.branch 51 (.leaf (-19)) (.leaf (-18))) (.branch 53 (.leaf (-17)) (.leaf (-16)))) (.branch 56 (.branch 55 (.leaf (-15)) (.leaf (-14))) (.branch 57 (.leaf (-13)) (.branch 58 (.leaf (-12)) (.leaf (-11)))))) (.branch 64 (.branch 61 (.branch 60 (.leaf (-10)) (.leaf (-9))) (.branch 62 (.leaf (-8)) (.branch 63 (.leaf (-7)) (.leaf (-6))))) (.branch 66 (.branch 65 (.leaf (-5)) (.leaf (-4))) (.branch 67 (.leaf (-3)) (.branch 68 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 65 (.branch 63 (.leaf (-7)) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 67 (.branch 66 (.leaf (-4)) (.leaf (-3))) (.branch 68 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_284_4710 : CycleWitness 9 where
  length := 69
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (6))) (.branch 11 (.leaf (8)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (7)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (5))) (.branch 20 (.leaf (2)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (8))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (4)) (.leaf (7))) (.branch 28 (.leaf (5)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (3))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (6)) (.leaf (8)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (4)) (.leaf (0))) (.branch 37 (.leaf (2)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (7)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (3))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (2)) (.leaf (6))) (.branch 45 (.leaf (4)) (.leaf (8)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (5)) (.branch 50 (.leaf (7)) (.leaf (3))))))) (.branch 60 (.branch 55 (.branch 53 (.branch 52 (.leaf (2)) (.leaf (0))) (.branch 54 (.leaf (4)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (6)) (.leaf (8))) (.branch 58 (.leaf (5)) (.branch 59 (.leaf (0)) (.leaf (2)))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (3)) (.leaf (7))) (.branch 63 (.leaf (1)) (.leaf (0)))) (.branch 66 (.branch 65 (.leaf (4)) (.leaf (2))) (.branch 67 (.leaf (6)) (.branch 68 (.leaf (5)) (.leaf (8)))))))))
  code := certificateP9_4710
  counts := ![(.branch 30 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 63 (.leaf (8)) (.leaf (9)))))),
  (.branch 37 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 60 (.leaf (7)) (.branch 66 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 65 (.leaf (6)) (.leaf (7))))),
  (.branch 38 (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 58 (.branch 49 (.leaf (4)) (.leaf (5))) (.branch 68 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 67 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 69 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-19)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-17)) (.leaf (-19)))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (-2))) (.branch 43 (.leaf (-4)) (.branch 66 (.leaf (-5)) (.leaf (-6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 31 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.branch 54 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-15))),
  (.branch 11 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 66 (.branch 65 (.leaf (-20)) (.leaf (-16))) (.branch 67 (.leaf (-12)) (.branch 68 (.leaf (-8)) (.leaf (-4))))),
  (.branch 65 (.branch 56 (.leaf (-19)) (.branch 64 (.leaf (-18)) (.leaf (-15)))) (.branch 67 (.branch 66 (.leaf (-12)) (.leaf (-9))) (.branch 68 (.leaf (-6)) (.leaf (-3))))),
  (.branch 67 (.leaf (-6)) (.branch 68 (.leaf (-5)) (.leaf (-4)))),
  (.branch 65 (.branch 63 (.branch 62 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-7)) (.leaf (-6)))) (.branch 67 (.branch 66 (.leaf (-5)) (.leaf (-4))) (.branch 68 (.leaf (-3)) (.leaf (-2))))),
  (.branch 66 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 67 (.leaf (-4)) (.branch 68 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 68 (.leaf (-4)) (.leaf (-2))),
  (.branch 65 (.branch 63 (.branch 51 (.leaf (-15)) (.leaf (-14))) (.branch 64 (.leaf (-12)) (.leaf (-10)))) (.branch 67 (.branch 66 (.leaf (-8)) (.leaf (-6))) (.branch 68 (.leaf (-4)) (.leaf (-2))))),
  (.branch 58 (.leaf (-1)) (.leaf (0)))]
def witnessP9_284_4711 : CycleWitness 9 where
  length := 69
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (6))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (8))) (.branch 11 (.leaf (1)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (7)) (.branch 16 (.leaf (6)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (1)) (.leaf (8)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (3))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (6)) (.leaf (7))) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (8)) (.leaf (3)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (6)) (.leaf (0))) (.branch 37 (.leaf (1)) (.leaf (7)))) (.branch 40 (.branch 39 (.leaf (4)) (.leaf (2))) (.branch 41 (.leaf (0)) (.leaf (5))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (3)) (.leaf (8))) (.branch 45 (.leaf (6)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (2))) (.branch 49 (.leaf (4)) (.branch 50 (.leaf (7)) (.leaf (3))))))) (.branch 60 (.branch 55 (.branch 53 (.branch 52 (.leaf (5)) (.leaf (0))) (.branch 54 (.leaf (1)) (.leaf (6)))) (.branch 57 (.branch 56 (.leaf (8)) (.leaf (2))) (.branch 58 (.leaf (4)) (.branch 59 (.leaf (0)) (.leaf (3)))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (7)) (.leaf (5))) (.branch 63 (.leaf (1)) (.leaf (0)))) (.branch 66 (.branch 65 (.leaf (6)) (.leaf (2))) (.branch 67 (.leaf (8)) (.branch 68 (.leaf (4)) (.leaf (3)))))))))
  code := certificateP9_4711
  counts := ![(.branch 30 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.branch 69 (.leaf (7)) (.leaf (8)))))),
  (.branch 39 (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 58 (.branch 49 (.leaf (4)) (.leaf (5))) (.branch 68 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 55 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 65 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 67 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-19)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.leaf (-53))),
  (.branch 5 (.leaf (0)) (.branch 48 (.leaf (-29)) (.leaf (-30)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-5)) (.leaf (-7)))),
  (.branch 9 (.leaf (0)) (.branch 58 (.leaf (-6)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-48)) (.leaf (-54)))),
  (.branch 6 (.leaf (0)) (.branch 35 (.leaf (-27)) (.leaf (-31)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-15)) (.leaf (-16)))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 66 (.branch 65 (.leaf (-20)) (.leaf (-16))) (.branch 67 (.leaf (-12)) (.branch 68 (.leaf (-8)) (.leaf (-4))))),
  (.branch 64 (.branch 29 (.branch 3 (.leaf (-53)) (.leaf (-52))) (.branch 55 (.leaf (-51)) (.leaf (-48)))) (.branch 66 (.branch 65 (.leaf (-40)) (.leaf (-32))) (.branch 67 (.leaf (-24)) (.branch 68 (.leaf (-16)) (.leaf (-8)))))),
  (.branch 58 (.branch 49 (.leaf (-30)) (.leaf (-27))) (.branch 67 (.leaf (-24)) (.branch 68 (.leaf (-16)) (.leaf (-8))))),
  (.branch 52 (.branch 26 (.leaf (-7)) (.leaf (-6))) (.branch 61 (.leaf (-3)) (.leaf (0)))),
  (.branch 59 (.leaf (-8)) (.leaf (-7))),
  (.branch 63 (.branch 33 (.branch 13 (.leaf (-54)) (.branch 23 (.leaf (-53)) (.leaf (-52)))) (.branch 43 (.leaf (-51)) (.branch 53 (.leaf (-50)) (.leaf (-49))))) (.branch 66 (.branch 64 (.leaf (-42)) (.branch 65 (.leaf (-35)) (.leaf (-28)))) (.branch 67 (.leaf (-21)) (.branch 68 (.leaf (-14)) (.leaf (-7)))))),
  (.branch 56 (.branch 36 (.leaf (-31)) (.branch 46 (.leaf (-30)) (.leaf (-29)))) (.branch 67 (.branch 66 (.leaf (-28)) (.leaf (-21))) (.branch 68 (.leaf (-14)) (.leaf (-7))))),
  (.branch 65 (.branch 63 (.branch 62 (.leaf (-16)) (.leaf (-14))) (.branch 64 (.leaf (-12)) (.leaf (-10)))) (.branch 67 (.branch 66 (.leaf (-8)) (.leaf (-6))) (.branch 68 (.leaf (-4)) (.leaf (-2))))),
  (.branch 68 (.leaf (-4)) (.leaf (-2)))]
def witnessP9_284_4712 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (4)) (.leaf (0))))) (.branch 13 (.branch 10 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (5)))))) (.branch 26 (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (7)) (.leaf (0))))) (.branch 30 (.branch 27 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (3)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.leaf (6))))))) (.branch 51 (.branch 43 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (4)) (.leaf (0))))) (.branch 47 (.branch 44 (.leaf (1)) (.branch 46 (.leaf (0)) (.leaf (3)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (0)) (.leaf (5)))))) (.branch 60 (.branch 56 (.branch 54 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (8)) (.leaf (0))))) (.branch 64 (.branch 61 (.leaf (1)) (.branch 63 (.leaf (0)) (.leaf (3)))) (.branch 66 (.branch 65 (.leaf (0)) (.leaf (1))) (.branch 67 (.leaf (0)) (.leaf (6))))))))
  code := certificateP9_4712
  counts := ![(.branch 33 (.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 12 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 20 (.leaf (12)) (.branch 22 (.leaf (13)) (.leaf (14))))) (.branch 28 (.branch 26 (.leaf (15)) (.leaf (16))) (.branch 29 (.leaf (17)) (.branch 31 (.leaf (18)) (.leaf (19))))))) (.branch 50 (.branch 41 (.branch 36 (.branch 35 (.leaf (20)) (.leaf (21))) (.branch 37 (.leaf (22)) (.branch 39 (.leaf (23)) (.leaf (24))))) (.branch 45 (.branch 43 (.leaf (25)) (.leaf (26))) (.branch 46 (.leaf (27)) (.branch 48 (.leaf (28)) (.leaf (29)))))) (.branch 58 (.branch 53 (.branch 52 (.leaf (30)) (.leaf (31))) (.branch 54 (.leaf (32)) (.branch 56 (.leaf (33)) (.leaf (34))))) (.branch 63 (.branch 60 (.leaf (35)) (.branch 62 (.leaf (36)) (.leaf (37)))) (.branch 65 (.leaf (38)) (.branch 67 (.leaf (39)) (.leaf (40)))))))),
  (.branch 32 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 61 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2)))),
  (.branch 34 (.leaf (0)) (.branch 68 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 59 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 37 (.branch 20 (.leaf (-9)) (.leaf (-11))) (.branch 54 (.leaf (-13)) (.leaf (-15))))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-26))),
  (.branch 17 (.leaf (0)) (.leaf (-17))),
  (.leaf (0)),
  (.branch 25 (.leaf (0)) (.leaf (-43))),
  (.branch 59 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 64 (.branch 55 (.leaf (-15)) (.leaf (-14))) (.branch 66 (.leaf (-13)) (.leaf (-12)))),
  (.branch 67 (.leaf (-6)) (.leaf (-3))),
  (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.branch 48 (.branch 45 (.branch 43 (.leaf (-26)) (.branch 44 (.leaf (-25)) (.leaf (-24)))) (.branch 46 (.leaf (-23)) (.branch 47 (.leaf (-22)) (.leaf (-21))))) (.branch 51 (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-19)) (.leaf (-18)))) (.branch 53 (.branch 52 (.leaf (-17)) (.leaf (-16))) (.branch 54 (.leaf (-15)) (.leaf (-14)))))) (.branch 61 (.branch 58 (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))) (.branch 59 (.leaf (-10)) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (-17)) (.leaf (-16))) (.branch 54 (.leaf (-15)) (.leaf (-14)))) (.branch 57 (.branch 56 (.leaf (-13)) (.leaf (-12))) (.branch 58 (.leaf (-11)) (.leaf (-10))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0)),
  (.branch 46 (.branch 35 (.branch 30 (.branch 27 (.branch 26 (.leaf (-43)) (.leaf (-42))) (.branch 28 (.leaf (-41)) (.branch 29 (.leaf (-40)) (.leaf (-39))))) (.branch 32 (.branch 31 (.leaf (-38)) (.leaf (-37))) (.branch 33 (.leaf (-36)) (.branch 34 (.leaf (-35)) (.leaf (-34)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-33)) (.leaf (-32))) (.branch 38 (.leaf (-31)) (.branch 39 (.leaf (-30)) (.leaf (-29))))) (.branch 43 (.branch 41 (.leaf (-28)) (.branch 42 (.leaf (-27)) (.leaf (-26)))) (.branch 44 (.leaf (-25)) (.branch 45 (.leaf (-24)) (.leaf (-23))))))) (.branch 57 (.branch 51 (.branch 48 (.branch 47 (.leaf (-22)) (.leaf (-21))) (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-19)) (.leaf (-18))))) (.branch 54 (.branch 52 (.leaf (-17)) (.branch 53 (.leaf (-16)) (.leaf (-15)))) (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))))) (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_284_4713 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (0))) (.branch 8 (.leaf (2)) (.leaf (0))))) (.branch 13 (.branch 10 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (3)))))) (.branch 26 (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 27 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (6)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.leaf (3))))))) (.branch 51 (.branch 43 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (4)) (.leaf (0))) (.branch 42 (.leaf (2)) (.leaf (0))))) (.branch 47 (.branch 44 (.leaf (1)) (.branch 46 (.leaf (0)) (.leaf (7)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (0)) (.leaf (3)))))) (.branch 60 (.branch 56 (.branch 54 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (4)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (0))))) (.branch 64 (.branch 61 (.leaf (1)) (.branch 63 (.leaf (0)) (.leaf (8)))) (.branch 66 (.branch 65 (.leaf (0)) (.leaf (1))) (.branch 67 (.leaf (0)) (.leaf (3))))))))
  code := certificateP9_4713
  counts := ![(.branch 33 (.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 12 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 20 (.leaf (12)) (.branch 22 (.leaf (13)) (.leaf (14))))) (.branch 28 (.branch 26 (.leaf (15)) (.leaf (16))) (.branch 29 (.leaf (17)) (.branch 31 (.leaf (18)) (.leaf (19))))))) (.branch 50 (.branch 41 (.branch 36 (.branch 35 (.leaf (20)) (.leaf (21))) (.branch 37 (.leaf (22)) (.branch 39 (.leaf (23)) (.leaf (24))))) (.branch 45 (.branch 43 (.leaf (25)) (.leaf (26))) (.branch 46 (.leaf (27)) (.branch 48 (.leaf (28)) (.leaf (29)))))) (.branch 58 (.branch 53 (.branch 52 (.leaf (30)) (.leaf (31))) (.branch 54 (.leaf (32)) (.branch 56 (.leaf (33)) (.leaf (34))))) (.branch 63 (.branch 60 (.leaf (35)) (.branch 62 (.leaf (36)) (.leaf (37)))) (.branch 65 (.leaf (38)) (.branch 67 (.leaf (39)) (.leaf (40)))))))),
  (.branch 32 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 61 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.branch 68 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1))),
  (.branch 64 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 37 (.branch 20 (.leaf (-9)) (.leaf (-11))) (.branch 54 (.leaf (-13)) (.leaf (-15))))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-55))),
  (.branch 30 (.leaf (0)) (.leaf (-38))),
  (.branch 47 (.leaf (0)) (.leaf (-21))),
  (.branch 64 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 64 (.branch 55 (.leaf (-15)) (.leaf (-14))) (.branch 66 (.leaf (-13)) (.leaf (-12)))),
  (.branch 67 (.leaf (-6)) (.leaf (-3))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 26 (.branch 19 (.branch 16 (.branch 14 (.leaf (-55)) (.branch 15 (.leaf (-54)) (.leaf (-53)))) (.branch 17 (.leaf (-52)) (.branch 18 (.leaf (-51)) (.leaf (-50))))) (.branch 22 (.branch 20 (.leaf (-49)) (.branch 21 (.leaf (-48)) (.leaf (-47)))) (.branch 24 (.branch 23 (.leaf (-46)) (.leaf (-45))) (.branch 25 (.leaf (-44)) (.leaf (-43)))))) (.branch 33 (.branch 29 (.branch 27 (.leaf (-42)) (.branch 28 (.leaf (-41)) (.leaf (-40)))) (.branch 31 (.branch 30 (.leaf (-39)) (.leaf (-38))) (.branch 32 (.leaf (-37)) (.leaf (-36))))) (.branch 36 (.branch 34 (.leaf (-35)) (.branch 35 (.leaf (-34)) (.leaf (-33)))) (.branch 38 (.branch 37 (.leaf (-32)) (.leaf (-31))) (.branch 39 (.leaf (-30)) (.leaf (-29))))))) (.branch 54 (.branch 47 (.branch 43 (.branch 41 (.leaf (-28)) (.branch 42 (.leaf (-27)) (.leaf (-26)))) (.branch 45 (.branch 44 (.leaf (-25)) (.leaf (-24))) (.branch 46 (.leaf (-23)) (.leaf (-22))))) (.branch 50 (.branch 48 (.leaf (-21)) (.branch 49 (.leaf (-20)) (.leaf (-19)))) (.branch 52 (.branch 51 (.leaf (-18)) (.leaf (-17))) (.branch 53 (.leaf (-16)) (.leaf (-15)))))) (.branch 61 (.branch 57 (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 39 (.branch 34 (.branch 32 (.branch 31 (.leaf (-38)) (.leaf (-37))) (.branch 33 (.leaf (-36)) (.leaf (-35)))) (.branch 36 (.branch 35 (.leaf (-34)) (.leaf (-33))) (.branch 37 (.leaf (-32)) (.branch 38 (.leaf (-31)) (.leaf (-30)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (-29)) (.leaf (-28))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-26)) (.leaf (-25))))) (.branch 46 (.branch 45 (.leaf (-24)) (.leaf (-23))) (.branch 47 (.leaf (-22)) (.branch 48 (.leaf (-21)) (.leaf (-20))))))) (.branch 58 (.branch 53 (.branch 51 (.branch 50 (.leaf (-19)) (.leaf (-18))) (.branch 52 (.leaf (-17)) (.leaf (-16)))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-14))) (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))))) (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 57 (.branch 52 (.branch 49 (.branch 48 (.leaf (-21)) (.leaf (-20))) (.branch 50 (.leaf (-19)) (.branch 51 (.leaf (-18)) (.leaf (-17))))) (.branch 54 (.branch 53 (.leaf (-16)) (.leaf (-15))) (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))))) (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_284_4714 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (6)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (7))) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.leaf (5))))))) (.branch 51 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (3))) (.branch 42 (.leaf (0)) (.leaf (1))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (4))) (.branch 46 (.leaf (0)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (0)) (.leaf (6)))))) (.branch 60 (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (0)) (.leaf (1))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (0)) (.leaf (8))) (.branch 63 (.leaf (0)) (.leaf (2)))) (.branch 66 (.branch 65 (.leaf (0)) (.leaf (1))) (.branch 67 (.leaf (0)) (.leaf (5))))))))
  code := certificateP9_4714
  counts := ![(.branch 33 (.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 23 (.branch 19 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.leaf (12)))) (.branch 27 (.branch 25 (.leaf (13)) (.leaf (14))) (.branch 29 (.leaf (15)) (.branch 31 (.leaf (16)) (.leaf (17))))))) (.branch 50 (.branch 40 (.branch 36 (.branch 35 (.leaf (18)) (.leaf (19))) (.branch 38 (.leaf (20)) (.leaf (21)))) (.branch 44 (.branch 42 (.leaf (22)) (.leaf (23))) (.branch 46 (.leaf (24)) (.branch 48 (.leaf (25)) (.leaf (26)))))) (.branch 59 (.branch 53 (.branch 52 (.leaf (27)) (.leaf (28))) (.branch 55 (.leaf (29)) (.branch 57 (.leaf (30)) (.leaf (31))))) (.branch 63 (.branch 61 (.leaf (32)) (.leaf (33))) (.branch 65 (.leaf (34)) (.branch 67 (.leaf (35)) (.leaf (36)))))))),
  (.branch 32 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 34 (.leaf (0)) (.branch 68 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 62 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-23))),
  (.leaf (0)),
  (.branch 17 (.leaf (0)) (.leaf (-17))),
  (.branch 28 (.leaf (0)) (.leaf (-40))),
  (.branch 62 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 60 (.branch 56 (.branch 54 (.leaf (-16)) (.leaf (-15))) (.branch 58 (.leaf (-14)) (.leaf (-13)))) (.branch 64 (.branch 62 (.leaf (-12)) (.leaf (-11))) (.branch 66 (.leaf (-10)) (.leaf (-9))))),
  (.branch 61 (.branch 55 (.leaf (-8)) (.leaf (-7))) (.branch 67 (.leaf (-6)) (.leaf (-3)))),
  (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-6))) (.branch 67 (.leaf (-4)) (.leaf (-2)))),
  (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 56 (.branch 50 (.branch 47 (.branch 46 (.leaf (-23)) (.leaf (-22))) (.branch 48 (.leaf (-21)) (.branch 49 (.leaf (-20)) (.leaf (-19))))) (.branch 53 (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-17)) (.leaf (-16)))) (.branch 54 (.leaf (-15)) (.branch 55 (.leaf (-14)) (.leaf (-13)))))) (.branch 62 (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-11)) (.leaf (-10)))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0)),
  (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (-17)) (.leaf (-16))) (.branch 54 (.leaf (-15)) (.leaf (-14)))) (.branch 57 (.branch 56 (.leaf (-13)) (.leaf (-12))) (.branch 58 (.leaf (-11)) (.leaf (-10))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 38 (.branch 33 (.branch 30 (.branch 29 (.leaf (-40)) (.leaf (-39))) (.branch 31 (.leaf (-38)) (.branch 32 (.leaf (-37)) (.leaf (-36))))) (.branch 35 (.branch 34 (.leaf (-35)) (.leaf (-34))) (.branch 36 (.leaf (-33)) (.branch 37 (.leaf (-32)) (.leaf (-31)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-30)) (.leaf (-29))) (.branch 41 (.leaf (-28)) (.branch 42 (.leaf (-27)) (.leaf (-26))))) (.branch 45 (.branch 44 (.leaf (-25)) (.leaf (-24))) (.branch 46 (.leaf (-23)) (.branch 47 (.leaf (-22)) (.leaf (-21))))))) (.branch 58 (.branch 53 (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-19))) (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-17)) (.leaf (-16))))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-14))) (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))))) (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_284_4715 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (5)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.leaf (6))))))) (.branch 51 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (4))) (.branch 42 (.leaf (0)) (.leaf (1))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (3))) (.branch 46 (.leaf (0)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (0)) (.leaf (7)))))) (.branch 60 (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (4))) (.branch 59 (.leaf (0)) (.leaf (1))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (0)) (.leaf (3))) (.branch 63 (.leaf (0)) (.leaf (2)))) (.branch 66 (.branch 65 (.leaf (0)) (.leaf (1))) (.branch 67 (.leaf (0)) (.leaf (8))))))))
  code := certificateP9_4715
  counts := ![(.branch 33 (.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 23 (.branch 19 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.leaf (12)))) (.branch 27 (.branch 25 (.leaf (13)) (.leaf (14))) (.branch 29 (.leaf (15)) (.branch 31 (.leaf (16)) (.leaf (17))))))) (.branch 50 (.branch 40 (.branch 36 (.branch 35 (.leaf (18)) (.leaf (19))) (.branch 38 (.leaf (20)) (.leaf (21)))) (.branch 44 (.branch 42 (.leaf (22)) (.leaf (23))) (.branch 46 (.leaf (24)) (.branch 48 (.leaf (25)) (.leaf (26)))))) (.branch 59 (.branch 53 (.branch 52 (.leaf (27)) (.leaf (28))) (.branch 55 (.leaf (29)) (.branch 57 (.leaf (30)) (.leaf (31))))) (.branch 63 (.branch 61 (.leaf (32)) (.leaf (33))) (.branch 65 (.leaf (34)) (.branch 67 (.leaf (35)) (.leaf (36)))))))),
  (.branch 32 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 51 (.leaf (0)) (.leaf (1))),
  (.branch 68 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-51))),
  (.branch 34 (.leaf (0)) (.leaf (-34))),
  (.branch 51 (.leaf (0)) (.leaf (-17))),
  (.leaf (0))]
  high := ![(.branch 60 (.branch 56 (.branch 54 (.leaf (-16)) (.leaf (-15))) (.branch 58 (.leaf (-14)) (.leaf (-13)))) (.branch 64 (.branch 62 (.leaf (-12)) (.leaf (-11))) (.branch 66 (.leaf (-10)) (.leaf (-9))))),
  (.branch 61 (.branch 55 (.leaf (-8)) (.leaf (-7))) (.branch 67 (.leaf (-6)) (.leaf (-3)))),
  (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-6))) (.branch 67 (.leaf (-4)) (.leaf (-2)))),
  (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))),
  (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 29 (.branch 23 (.branch 20 (.branch 18 (.leaf (-51)) (.branch 19 (.leaf (-50)) (.leaf (-49)))) (.branch 21 (.leaf (-48)) (.branch 22 (.leaf (-47)) (.leaf (-46))))) (.branch 26 (.branch 24 (.leaf (-45)) (.branch 25 (.leaf (-44)) (.leaf (-43)))) (.branch 27 (.leaf (-42)) (.branch 28 (.leaf (-41)) (.leaf (-40)))))) (.branch 35 (.branch 32 (.branch 30 (.leaf (-39)) (.branch 31 (.leaf (-38)) (.leaf (-37)))) (.branch 33 (.leaf (-36)) (.branch 34 (.leaf (-35)) (.leaf (-34))))) (.branch 38 (.branch 36 (.leaf (-33)) (.branch 37 (.leaf (-32)) (.leaf (-31)))) (.branch 40 (.branch 39 (.leaf (-30)) (.leaf (-29))) (.branch 41 (.leaf (-28)) (.leaf (-27))))))) (.branch 55 (.branch 48 (.branch 45 (.branch 43 (.leaf (-26)) (.branch 44 (.leaf (-25)) (.leaf (-24)))) (.branch 46 (.leaf (-23)) (.branch 47 (.leaf (-22)) (.leaf (-21))))) (.branch 51 (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-19)) (.leaf (-18)))) (.branch 53 (.branch 52 (.leaf (-17)) (.leaf (-16))) (.branch 54 (.leaf (-15)) (.leaf (-14)))))) (.branch 61 (.branch 58 (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))) (.branch 59 (.leaf (-10)) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (-34)) (.leaf (-33))) (.branch 37 (.leaf (-32)) (.leaf (-31)))) (.branch 40 (.branch 39 (.leaf (-30)) (.leaf (-29))) (.branch 41 (.leaf (-28)) (.leaf (-27))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-26)) (.leaf (-25))) (.branch 45 (.leaf (-24)) (.leaf (-23)))) (.branch 48 (.branch 47 (.leaf (-22)) (.leaf (-21))) (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-19)) (.leaf (-18))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (-17)) (.leaf (-16))) (.branch 54 (.leaf (-15)) (.leaf (-14)))) (.branch 57 (.branch 56 (.leaf (-13)) (.leaf (-12))) (.branch 58 (.leaf (-11)) (.leaf (-10))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (-17)) (.leaf (-16))) (.branch 54 (.leaf (-15)) (.leaf (-14)))) (.branch 57 (.branch 56 (.leaf (-13)) (.leaf (-12))) (.branch 58 (.leaf (-11)) (.leaf (-10))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_284_4716 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (1)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (7)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (1)) (.leaf (0))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (5)) (.leaf (0))) (.branch 33 (.leaf (1)) (.leaf (3))))))) (.branch 51 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (4))) (.branch 42 (.leaf (1)) (.leaf (0))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (3)) (.leaf (0))) (.branch 46 (.leaf (1)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (8)) (.leaf (0))) (.branch 50 (.leaf (1)) (.leaf (2)))))) (.branch 60 (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (4))) (.branch 59 (.leaf (1)) (.leaf (0))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (2)) (.leaf (0))) (.branch 63 (.leaf (1)) (.leaf (0)))) (.branch 66 (.branch 65 (.leaf (6)) (.leaf (0))) (.branch 67 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_4716
  counts := ![(.branch 32 (.branch 15 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 23 (.branch 19 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 21 (.leaf (10)) (.leaf (11)))) (.branch 28 (.branch 26 (.leaf (12)) (.leaf (13))) (.branch 30 (.leaf (14)) (.leaf (15)))))) (.branch 49 (.branch 40 (.branch 36 (.branch 35 (.leaf (16)) (.leaf (17))) (.branch 38 (.leaf (18)) (.leaf (19)))) (.branch 45 (.branch 43 (.leaf (20)) (.leaf (21))) (.branch 47 (.leaf (22)) (.leaf (23))))) (.branch 57 (.branch 53 (.branch 52 (.leaf (24)) (.leaf (25))) (.branch 55 (.leaf (26)) (.leaf (27)))) (.branch 62 (.branch 60 (.leaf (28)) (.leaf (29))) (.branch 64 (.leaf (30)) (.branch 66 (.leaf (31)) (.leaf (32)))))))),
  (.branch 33 (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 50 (.branch 42 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 59 (.branch 54 (.leaf (12)) (.leaf (13))) (.branch 63 (.leaf (14)) (.branch 67 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 65 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 23 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))) (.branch 19 (.branch 6 (.leaf (-13)) (.leaf (-14))) (.branch 21 (.leaf (-15)) (.leaf (-16))))) (.branch 40 (.branch 36 (.leaf (-17)) (.branch 38 (.leaf (-18)) (.leaf (-19)))) (.branch 55 (.branch 53 (.leaf (-20)) (.leaf (-21))) (.branch 57 (.leaf (-22)) (.leaf (-23)))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 27 (.branch 5 (.leaf (0)) (.leaf (-13))) (.branch 61 (.leaf (-15)) (.leaf (-16)))),
  (.branch 10 (.leaf (0)) (.branch 44 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 31 (.leaf (0)) (.leaf (-37))),
  (.branch 65 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-54))),
  (.branch 48 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 58 (.leaf (-23)) (.branch 67 (.leaf (-22)) (.leaf (-17)))),
  (.branch 55 (.leaf (-5)) (.leaf (-4))),
  (.branch 64 (.branch 62 (.leaf (-16)) (.branch 63 (.leaf (-14)) (.leaf (-12)))) (.branch 66 (.branch 65 (.leaf (-10)) (.leaf (-8))) (.branch 67 (.leaf (-6)) (.leaf (-4))))),
  (.branch 57 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 58 (.leaf (-1)) (.leaf (0)))),
  (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 49 (.branch 40 (.branch 35 (.branch 33 (.branch 32 (.leaf (-37)) (.leaf (-36))) (.branch 34 (.leaf (-35)) (.leaf (-34)))) (.branch 37 (.branch 36 (.leaf (-33)) (.leaf (-32))) (.branch 38 (.leaf (-31)) (.branch 39 (.leaf (-30)) (.leaf (-29)))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-28)) (.leaf (-27))) (.branch 43 (.leaf (-26)) (.leaf (-25)))) (.branch 46 (.branch 45 (.leaf (-24)) (.leaf (-23))) (.branch 47 (.leaf (-22)) (.branch 48 (.leaf (-21)) (.leaf (-20))))))) (.branch 58 (.branch 53 (.branch 51 (.branch 50 (.leaf (-19)) (.leaf (-18))) (.branch 52 (.leaf (-17)) (.leaf (-16)))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-14))) (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))))) (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))),
  (.branch 41 (.branch 27 (.branch 20 (.branch 17 (.branch 15 (.leaf (-54)) (.branch 16 (.leaf (-53)) (.leaf (-52)))) (.branch 18 (.leaf (-51)) (.branch 19 (.leaf (-50)) (.leaf (-49))))) (.branch 23 (.branch 21 (.leaf (-48)) (.branch 22 (.leaf (-47)) (.leaf (-46)))) (.branch 25 (.branch 24 (.leaf (-45)) (.leaf (-44))) (.branch 26 (.leaf (-43)) (.leaf (-42)))))) (.branch 34 (.branch 30 (.branch 28 (.leaf (-41)) (.branch 29 (.leaf (-40)) (.leaf (-39)))) (.branch 32 (.branch 31 (.leaf (-38)) (.leaf (-37))) (.branch 33 (.leaf (-36)) (.leaf (-35))))) (.branch 37 (.branch 35 (.leaf (-34)) (.branch 36 (.leaf (-33)) (.leaf (-32)))) (.branch 39 (.branch 38 (.leaf (-31)) (.leaf (-30))) (.branch 40 (.leaf (-29)) (.leaf (-28))))))) (.branch 54 (.branch 47 (.branch 44 (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-26)) (.leaf (-25)))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-23)) (.leaf (-22))))) (.branch 50 (.branch 48 (.leaf (-21)) (.branch 49 (.leaf (-20)) (.leaf (-19)))) (.branch 52 (.branch 51 (.leaf (-18)) (.leaf (-17))) (.branch 53 (.leaf (-16)) (.leaf (-15)))))) (.branch 61 (.branch 57 (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 58 (.branch 53 (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-19))) (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-17)) (.leaf (-16))))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-14))) (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))))) (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_284_4717 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (1)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (1)) (.leaf (0))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (7)) (.leaf (0))) (.branch 33 (.leaf (1)) (.leaf (3))))))) (.branch 51 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (5))) (.branch 42 (.leaf (1)) (.leaf (0))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (3)) (.leaf (0))) (.branch 46 (.leaf (1)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (4)) (.leaf (0))) (.branch 50 (.leaf (1)) (.leaf (2)))))) (.branch 60 (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (6))) (.branch 59 (.leaf (1)) (.leaf (0))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (2)) (.leaf (0))) (.branch 63 (.leaf (1)) (.leaf (0)))) (.branch 66 (.branch 65 (.leaf (8)) (.leaf (0))) (.branch 67 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_4717
  counts := ![(.branch 32 (.branch 15 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 23 (.branch 19 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 21 (.leaf (10)) (.leaf (11)))) (.branch 28 (.branch 26 (.leaf (12)) (.leaf (13))) (.branch 30 (.leaf (14)) (.leaf (15)))))) (.branch 49 (.branch 40 (.branch 36 (.branch 35 (.leaf (16)) (.leaf (17))) (.branch 38 (.leaf (18)) (.leaf (19)))) (.branch 45 (.branch 43 (.leaf (20)) (.leaf (21))) (.branch 47 (.leaf (22)) (.leaf (23))))) (.branch 57 (.branch 53 (.branch 52 (.leaf (24)) (.leaf (25))) (.branch 55 (.leaf (26)) (.leaf (27)))) (.branch 62 (.branch 60 (.leaf (28)) (.leaf (29))) (.branch 64 (.leaf (30)) (.branch 66 (.leaf (31)) (.leaf (32)))))))),
  (.branch 33 (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 50 (.branch 42 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 59 (.branch 54 (.leaf (12)) (.leaf (13))) (.branch 63 (.leaf (14)) (.branch 67 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 58 (.leaf (1)) (.leaf (2)))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 65 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 23 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))) (.branch 19 (.branch 6 (.leaf (-13)) (.leaf (-14))) (.branch 21 (.leaf (-15)) (.leaf (-16))))) (.branch 40 (.branch 36 (.leaf (-17)) (.branch 38 (.leaf (-18)) (.leaf (-19)))) (.branch 55 (.branch 53 (.leaf (-20)) (.leaf (-21))) (.branch 57 (.leaf (-22)) (.leaf (-23)))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 27 (.branch 5 (.leaf (0)) (.leaf (-13))) (.branch 61 (.leaf (-15)) (.leaf (-16)))),
  (.branch 10 (.leaf (0)) (.branch 44 (.leaf (-3)) (.leaf (-4)))),
  (.branch 14 (.leaf (0)) (.leaf (-20))),
  (.branch 7 (.leaf (0)) (.leaf (-27))),
  (.branch 24 (.leaf (0)) (.leaf (-10))),
  (.branch 31 (.leaf (0)) (.leaf (-37))),
  (.branch 65 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 58 (.leaf (-23)) (.branch 67 (.leaf (-22)) (.leaf (-17)))),
  (.branch 55 (.leaf (-5)) (.leaf (-4))),
  (.branch 64 (.branch 62 (.leaf (-16)) (.branch 63 (.leaf (-14)) (.leaf (-12)))) (.branch 66 (.branch 65 (.leaf (-10)) (.leaf (-8))) (.branch 67 (.leaf (-6)) (.leaf (-4))))),
  (.branch 57 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 58 (.leaf (-1)) (.leaf (0)))),
  (.branch 58 (.branch 53 (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-19))) (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-17)) (.leaf (-16))))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-14))) (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))))) (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 47 (.branch 44 (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-26)) (.leaf (-25)))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-23)) (.leaf (-22))))) (.branch 50 (.branch 48 (.leaf (-21)) (.branch 49 (.leaf (-20)) (.leaf (-19)))) (.branch 52 (.branch 51 (.leaf (-18)) (.leaf (-17))) (.branch 53 (.leaf (-16)) (.leaf (-15)))))) (.branch 61 (.branch 57 (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 49 (.branch 40 (.branch 35 (.branch 33 (.branch 32 (.leaf (-37)) (.leaf (-36))) (.branch 34 (.leaf (-35)) (.leaf (-34)))) (.branch 37 (.branch 36 (.leaf (-33)) (.leaf (-32))) (.branch 38 (.leaf (-31)) (.branch 39 (.leaf (-30)) (.leaf (-29)))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-28)) (.leaf (-27))) (.branch 43 (.leaf (-26)) (.leaf (-25)))) (.branch 46 (.branch 45 (.leaf (-24)) (.leaf (-23))) (.branch 47 (.leaf (-22)) (.branch 48 (.leaf (-21)) (.leaf (-20))))))) (.branch 58 (.branch 53 (.branch 51 (.branch 50 (.leaf (-19)) (.leaf (-18))) (.branch 52 (.leaf (-17)) (.leaf (-16)))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-14))) (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))))) (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_284_4718 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (4)) (.leaf (0))))) (.branch 13 (.branch 10 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (6))) (.branch 16 (.leaf (0)) (.leaf (5)))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (0))))) (.branch 30 (.branch 27 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (7))) (.branch 33 (.leaf (0)) (.leaf (5))))))) (.branch 51 (.branch 43 (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 41 (.branch 39 (.leaf (3)) (.leaf (0))) (.branch 42 (.leaf (4)) (.leaf (0))))) (.branch 47 (.branch 44 (.leaf (1)) (.branch 46 (.leaf (0)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (6))) (.branch 50 (.leaf (0)) (.leaf (5)))))) (.branch 60 (.branch 55 (.branch 53 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 56 (.leaf (3)) (.leaf (0))) (.branch 59 (.leaf (4)) (.leaf (0))))) (.branch 64 (.branch 61 (.leaf (1)) (.branch 63 (.leaf (0)) (.leaf (2)))) (.branch 66 (.branch 65 (.leaf (0)) (.leaf (8))) (.branch 67 (.leaf (0)) (.leaf (5))))))))
  code := certificateP9_4718
  counts := ![(.branch 33 (.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 12 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 21 (.leaf (12)) (.branch 23 (.leaf (13)) (.leaf (14))))) (.branch 28 (.branch 26 (.leaf (15)) (.leaf (16))) (.branch 29 (.leaf (17)) (.branch 31 (.leaf (18)) (.leaf (19))))))) (.branch 50 (.branch 41 (.branch 36 (.branch 35 (.leaf (20)) (.leaf (21))) (.branch 38 (.leaf (22)) (.branch 40 (.leaf (23)) (.leaf (24))))) (.branch 45 (.branch 43 (.leaf (25)) (.leaf (26))) (.branch 46 (.leaf (27)) (.branch 48 (.leaf (28)) (.leaf (29)))))) (.branch 58 (.branch 53 (.branch 52 (.leaf (30)) (.leaf (31))) (.branch 55 (.leaf (32)) (.branch 57 (.leaf (33)) (.leaf (34))))) (.branch 63 (.branch 60 (.leaf (35)) (.branch 62 (.leaf (36)) (.leaf (37)))) (.branch 65 (.leaf (38)) (.branch 67 (.leaf (39)) (.leaf (40)))))))),
  (.branch 27 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.branch 68 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2)))),
  (.branch 32 (.leaf (0)) (.leaf (1))),
  (.branch 66 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-14)) (.branch 12 (.leaf (-15)) (.leaf (-16))))),
  (.branch 27 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-6)) (.leaf (-8)))) (.branch 44 (.leaf (-9)) (.branch 61 (.leaf (-10)) (.leaf (-11))))),
  (.branch 13 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 15 (.leaf (0)) (.leaf (-19))),
  (.branch 32 (.leaf (0)) (.leaf (-36))),
  (.branch 66 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 64 (.leaf (-16)) (.branch 66 (.leaf (-13)) (.leaf (-10)))),
  (.branch 64 (.branch 62 (.leaf (-11)) (.branch 63 (.leaf (-10)) (.leaf (-9)))) (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-7))) (.branch 67 (.leaf (-6)) (.leaf (-5))))),
  (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))),
  (.branch 62 (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-11)) (.leaf (-10)))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 58 (.branch 53 (.branch 51 (.branch 50 (.leaf (-19)) (.leaf (-18))) (.branch 52 (.leaf (-17)) (.leaf (-16)))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-14))) (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))))) (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 41 (.branch 36 (.branch 34 (.branch 33 (.leaf (-36)) (.leaf (-35))) (.branch 35 (.leaf (-34)) (.leaf (-33)))) (.branch 38 (.branch 37 (.leaf (-32)) (.leaf (-31))) (.branch 39 (.leaf (-30)) (.branch 40 (.leaf (-29)) (.leaf (-28)))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-27)) (.leaf (-26))) (.branch 44 (.leaf (-25)) (.leaf (-24)))) (.branch 47 (.branch 46 (.leaf (-23)) (.leaf (-22))) (.branch 48 (.leaf (-21)) (.branch 49 (.leaf (-20)) (.leaf (-19))))))) (.branch 59 (.branch 54 (.branch 52 (.branch 51 (.leaf (-18)) (.leaf (-17))) (.branch 53 (.leaf (-16)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-14)) (.leaf (-13))) (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-11)) (.leaf (-10)))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 67 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_284 : Fin 43 → CycleWitness 9 := ![witnessP9_284_4676, witnessP9_284_4677, witnessP9_284_4678, witnessP9_284_4679, witnessP9_284_4680, witnessP9_284_4681, witnessP9_284_4682, witnessP9_284_4683, witnessP9_284_4684, witnessP9_284_4685, witnessP9_284_4686, witnessP9_284_4687, witnessP9_284_4688, witnessP9_284_4689, witnessP9_284_4690, witnessP9_284_4691, witnessP9_284_4692, witnessP9_284_4693, witnessP9_284_4694, witnessP9_284_4695, witnessP9_284_4696, witnessP9_284_4697, witnessP9_284_4698, witnessP9_284_4699, witnessP9_284_4700, witnessP9_284_4701, witnessP9_284_4702, witnessP9_284_4703, witnessP9_284_4704, witnessP9_284_4705, witnessP9_284_4706, witnessP9_284_4707, witnessP9_284_4708, witnessP9_284_4709, witnessP9_284_4710, witnessP9_284_4711, witnessP9_284_4712, witnessP9_284_4713, witnessP9_284_4714, witnessP9_284_4715, witnessP9_284_4716, witnessP9_284_4717, witnessP9_284_4718]
end RealPinwheel.FiveSixths


