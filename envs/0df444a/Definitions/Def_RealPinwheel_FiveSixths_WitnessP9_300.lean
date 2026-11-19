-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_300
-- name    : RealPinwheel_FiveSixths_WitnessP9_300
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:27:03.565412+00:00
-- url     : https://prove2.me/theorems/b6ba4476-314a-4d99-b194-23b82964a521
-- title:
--   Exact witness block P9_300
-- statement:
--   These exact witnesses represent words 5416 through 5465 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 5416–5465; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_300_5415 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (7)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (3))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (4))) (.branch 14 (.leaf (0)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (8)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (6))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (7)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (8)) (.leaf (6))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (4))) (.branch 44 (.leaf (0)) (.leaf (5)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (7)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (6))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (8)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (3)) (.leaf (5))))))))
  code := certificateP9_5415
  counts := ![(.branch 28 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 44 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 48 (.leaf (14)) (.leaf (15))) (.branch 54 (.leaf (16)) (.branch 58 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 55 (.leaf (-8)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 57 (.branch 48 (.leaf (-11)) (.branch 56 (.leaf (-10)) (.leaf (-8)))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1)),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_300_5416 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (5))) (.branch 10 (.leaf (0)) (.leaf (8)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (6))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (7)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (5)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (6))) (.branch 40 (.leaf (0)) (.leaf (8)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (3)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (3))) (.branch 55 (.leaf (0)) (.leaf (7)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (6)) (.leaf (2))))))))
  code := certificateP9_5416
  counts := ![(.branch 28 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 40 (.leaf (13)) (.leaf (14))))) (.branch 52 (.branch 46 (.leaf (15)) (.branch 49 (.leaf (16)) (.leaf (17)))) (.branch 55 (.leaf (18)) (.branch 58 (.leaf (19)) (.leaf (20))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.leaf (0)) (.branch 56 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 39 (.leaf (0)) (.leaf (-1))),
  (.branch 26 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-19)))]
  high := ![(.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 58 (.branch 52 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.branch 51 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 50 (.branch 45 (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_300_5417 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (6))) (.branch 10 (.leaf (0)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (7)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (8))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (5))) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (6)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (7))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (8))) (.branch 40 (.leaf (0)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (5)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (6))) (.branch 51 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (7))) (.branch 55 (.leaf (0)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (8)) (.leaf (2))))))))
  code := certificateP9_5417
  counts := ![(.branch 28 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 40 (.leaf (13)) (.leaf (14))))) (.branch 52 (.branch 46 (.leaf (15)) (.branch 49 (.leaf (16)) (.leaf (17)))) (.branch 55 (.leaf (18)) (.branch 58 (.leaf (19)) (.leaf (20))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-15)) (.leaf (-16)))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 39 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 58 (.branch 52 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.branch 51 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessP9_300_5418 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (6)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (7)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (8))) (.branch 21 (.leaf (1)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (5)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (7))) (.branch 36 (.leaf (1)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (8)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (3)) (.leaf (1))) (.branch 44 (.leaf (0)) (.leaf (5)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (6))) (.branch 51 (.leaf (1)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (7)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (8))))))))
  code := certificateP9_5418
  counts := ![(.branch 29 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 44 (.branch 34 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 38 (.leaf (12)) (.branch 41 (.leaf (13)) (.leaf (14))))) (.branch 53 (.branch 46 (.leaf (15)) (.branch 49 (.leaf (16)) (.leaf (17)))) (.branch 56 (.leaf (18)) (.branch 59 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 50 (.leaf (-2)) (.leaf (-1))),
  (.branch 55 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-4)))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessP9_300_5419 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (7)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (3)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (8)) (.branch 17 (.leaf (0)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (3))) (.branch 21 (.leaf (5)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (6)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (7)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (5))) (.branch 36 (.leaf (8)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (3)) (.leaf (6)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (2)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (7)) (.branch 47 (.leaf (0)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (3))) (.branch 51 (.leaf (5)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (1))) (.branch 55 (.leaf (6)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (8)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5419
  counts := ![(.branch 26 (.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 39 (.leaf (9)) (.leaf (10)))) (.branch 52 (.branch 47 (.leaf (11)) (.leaf (12))) (.branch 56 (.leaf (13)) (.leaf (14)))))),
  (.branch 28 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 45 (.branch 37 (.branch 32 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 54 (.branch 49 (.leaf (11)) (.leaf (12))) (.branch 58 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 34 (.leaf (-14)) (.leaf (-15)))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))) (.branch 45 (.branch 32 (.leaf (-7)) (.leaf (-8))) (.branch 49 (.leaf (-9)) (.leaf (-10))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (-2))) (.branch 44 (.leaf (-3)) (.branch 59 (.leaf (-4)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 57 (.branch 48 (.leaf (-15)) (.leaf (-14))) (.branch 58 (.leaf (-11)) (.branch 59 (.leaf (-8)) (.leaf (-5))))),
  (.branch 59 (.leaf (-10)) (.leaf (-8))),
  (.leaf (-5)),
  (.leaf (0)),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 55 (.branch 52 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_300_5420 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (6))) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (0))) (.branch 10 (.leaf (3)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (1)) (.leaf (7)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (8)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (5))) (.branch 29 (.leaf (0)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (6))) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (5)) (.leaf (1))) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (4))) (.branch 44 (.leaf (0)) (.leaf (7)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (2)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (1))) (.branch 55 (.leaf (8)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (5))) (.branch 59 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_5420
  counts := ![(.branch 29 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.leaf (15)))))),
  (.branch 31 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 39 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 51 (.leaf (12)) (.leaf (13))) (.branch 59 (.leaf (14)) (.leaf (15)))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-25))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.branch 25 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.branch 41 (.branch 38 (.branch 36 (.leaf (-25)) (.branch 37 (.leaf (-24)) (.leaf (-23)))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))) (.branch 44 (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17)))) (.branch 45 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_300_5421 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (6))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (1))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (5))) (.branch 14 (.leaf (0)) (.leaf (8)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (6))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (7)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (1)) (.leaf (8))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (6))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (7)) (.leaf (2))) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (5))) (.branch 44 (.leaf (0)) (.leaf (8)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (6))) (.branch 51 (.leaf (0)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (7)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (5))) (.branch 59 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_5421
  counts := ![(.branch 27 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 44 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 47 (.leaf (14)) (.leaf (15))) (.branch 54 (.leaf (16)) (.branch 57 (.leaf (17)) (.leaf (18))))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 56 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 59 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 57 (.branch 43 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3))))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessP9_300_5422 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (7)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (3)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (5)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (0))) (.branch 44 (.leaf (3)) (.leaf (8)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (5)) (.leaf (0))) (.branch 59 (.leaf (3)) (.leaf (6))))))))
  code := certificateP9_5422
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 40 (.leaf (13)) (.leaf (14))))) (.branch 52 (.branch 46 (.leaf (15)) (.branch 50 (.leaf (16)) (.leaf (17)))) (.branch 55 (.leaf (18)) (.branch 58 (.leaf (19)) (.leaf (20))))))),
  (.branch 24 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.leaf (0)) (.branch 60 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 15 (.leaf (0)) (.leaf (-45))),
  (.branch 45 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-10)) (.leaf (-8)))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-6))) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.leaf (-3)) (.leaf (-2))),
  (.branch 56 (.branch 54 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 37 (.branch 26 (.branch 20 (.branch 17 (.branch 16 (.leaf (-45)) (.leaf (-44))) (.branch 18 (.leaf (-43)) (.branch 19 (.leaf (-42)) (.leaf (-41))))) (.branch 23 (.branch 21 (.leaf (-40)) (.branch 22 (.leaf (-39)) (.leaf (-38)))) (.branch 24 (.leaf (-37)) (.branch 25 (.leaf (-36)) (.leaf (-35)))))) (.branch 31 (.branch 28 (.branch 27 (.leaf (-34)) (.leaf (-33))) (.branch 29 (.leaf (-32)) (.branch 30 (.leaf (-31)) (.leaf (-30))))) (.branch 34 (.branch 32 (.leaf (-29)) (.branch 33 (.leaf (-28)) (.leaf (-27)))) (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24))))))) (.branch 48 (.branch 42 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_300_5423 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (5)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (7)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (6)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (3)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (5)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (2)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (8)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (0))) (.branch 55 (.leaf (6)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5423
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 14 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 15 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 36 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 3 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-27))),
  (.branch 10 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-5))),
  (.branch 18 (.leaf (0)) (.leaf (-42))),
  (.branch 48 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 51 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-4))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 54 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 46 (.branch 39 (.branch 36 (.branch 34 (.leaf (-27)) (.branch 35 (.leaf (-26)) (.leaf (-25)))) (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22))))) (.branch 42 (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19)))) (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 28 (.branch 23 (.branch 20 (.branch 19 (.leaf (-42)) (.leaf (-41))) (.branch 21 (.leaf (-40)) (.branch 22 (.leaf (-39)) (.leaf (-38))))) (.branch 25 (.branch 24 (.leaf (-37)) (.leaf (-36))) (.branch 26 (.leaf (-35)) (.branch 27 (.leaf (-34)) (.leaf (-33)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28))))) (.branch 36 (.branch 34 (.leaf (-27)) (.branch 35 (.leaf (-26)) (.leaf (-25)))) (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22))))))) (.branch 49 (.branch 44 (.branch 41 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17))))) (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_300_5424 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (0))) (.branch 10 (.leaf (6)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (7)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (2)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (3)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (5)) (.leaf (0))) (.branch 40 (.leaf (6)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (4))) (.branch 44 (.leaf (1)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (8)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (5))) (.branch 59 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5424
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 55 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (-2))) (.branch 36 (.leaf (-3)) (.branch 51 (.leaf (-4)) (.leaf (-5))))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-35))),
  (.branch 55 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-8)) (.leaf (-4)))),
  (.branch 57 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 54 (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))) (.branch 55 (.leaf (-2)) (.branch 56 (.leaf (-1)) (.leaf (0))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-35)) (.leaf (-34))) (.branch 28 (.leaf (-33)) (.leaf (-32)))) (.branch 31 (.branch 30 (.leaf (-31)) (.leaf (-30))) (.branch 32 (.leaf (-29)) (.leaf (-28))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))))) (.branch 51 (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_300_5425 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (7))) (.branch 10 (.leaf (4)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (3))) (.branch 14 (.leaf (1)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (8)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (4))) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (7))) (.branch 29 (.leaf (3)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (3))) (.branch 36 (.leaf (0)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (5)) (.leaf (8))) (.branch 40 (.leaf (4)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (3))) (.branch 44 (.leaf (1)) (.leaf (6)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (7)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (4))) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (8))) (.branch 59 (.leaf (3)) (.leaf (6))))))))
  code := certificateP9_5425
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.branch 35 (.leaf (-3)) (.leaf (-5)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))) (.branch 47 (.branch 24 (.leaf (-7)) (.leaf (-8))) (.branch 54 (.leaf (-9)) (.leaf (-10))))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (-11)) (.leaf (-12)))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 35 (.leaf (-7)) (.leaf (-6))) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-5)),
  (.branch 57 (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8)))) (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_300_5426 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (6)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (1))) (.branch 29 (.leaf (5)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (0))) (.branch 36 (.leaf (2)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (7)) (.leaf (0))) (.branch 40 (.leaf (2)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (8)) (.leaf (2))))))))
  code := certificateP9_5426
  counts := ![(.branch 26 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 44 (.branch 35 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 39 (.leaf (9)) (.leaf (10)))) (.branch 52 (.branch 47 (.leaf (11)) (.leaf (12))) (.branch 56 (.leaf (13)) (.leaf (14)))))),
  (.branch 28 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 46 (.branch 37 (.branch 32 (.leaf (7)) (.leaf (8))) (.branch 41 (.leaf (9)) (.leaf (10)))) (.branch 54 (.branch 50 (.leaf (11)) (.leaf (12))) (.branch 58 (.leaf (13)) (.leaf (14)))))),
  (.branch 30 (.branch 15 (.branch 6 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 36 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1))),
  (.branch 59 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))) (.branch 17 (.leaf (-12)) (.branch 47 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.branch 32 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-42))),
  (.branch 38 (.leaf (0)) (.leaf (-22))),
  (.branch 59 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 57 (.branch 48 (.leaf (-15)) (.leaf (-14))) (.branch 58 (.leaf (-11)) (.branch 59 (.leaf (-8)) (.leaf (-5))))),
  (.branch 59 (.leaf (-8)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 58 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 28 (.branch 23 (.branch 20 (.branch 19 (.leaf (-42)) (.leaf (-41))) (.branch 21 (.leaf (-40)) (.branch 22 (.leaf (-39)) (.leaf (-38))))) (.branch 25 (.branch 24 (.leaf (-37)) (.leaf (-36))) (.branch 26 (.leaf (-35)) (.branch 27 (.leaf (-34)) (.leaf (-33)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28))))) (.branch 36 (.branch 34 (.leaf (-27)) (.branch 35 (.leaf (-26)) (.leaf (-25)))) (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22))))))) (.branch 49 (.branch 44 (.branch 41 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17))))) (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 43 (.branch 40 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18))))) (.branch 46 (.branch 44 (.leaf (-17)) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_300_5427 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (7))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (1))) (.branch 10 (.leaf (6)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (8)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (5)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (7))) (.branch 21 (.leaf (1)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (6)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (8)) (.leaf (1))) (.branch 29 (.leaf (5)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (7))) (.branch 36 (.leaf (6)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (1))) (.branch 40 (.leaf (5)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (8)) (.leaf (0))) (.branch 44 (.leaf (4)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (6)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (7))) (.branch 51 (.leaf (1)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (4))) (.branch 55 (.leaf (0)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (8)) (.leaf (1))) (.branch 59 (.leaf (6)) (.leaf (2))))))))
  code := certificateP9_5427
  counts := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 32 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 32 (.leaf (-10)) (.branch 51 (.leaf (-14)) (.leaf (-15))))),
  (.branch 22 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 18 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-13))) (.branch 29 (.leaf (-16)) (.branch 40 (.leaf (-17)) (.leaf (-20))))),
  (.branch 47 (.branch 10 (.leaf (0)) (.leaf (-5))) (.branch 59 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 12 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.leaf (-15)) (.branch 59 (.leaf (-14)) (.leaf (-12)))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 57 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 56 (.branch 34 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 54 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 55 (.leaf (-17)) (.leaf (-15)))) (.branch 58 (.branch 57 (.leaf (-13)) (.leaf (-11))) (.branch 59 (.leaf (-9)) (.leaf (-7))))),
  (.leaf (-7)),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_300_5428 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (8)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (1)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (6))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (7)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (5)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (0))) (.branch 36 (.leaf (2)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (3)) (.leaf (0))) (.branch 40 (.leaf (8)) (.leaf (5)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (4))) (.branch 44 (.leaf (1)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (6)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (5))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (7)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (6)) (.leaf (2))))))))
  code := certificateP9_5428
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (-2))) (.branch 36 (.leaf (-3)) (.branch 51 (.leaf (-4)) (.leaf (-5))))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 25 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-8)) (.leaf (-4)))),
  (.branch 57 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))) (.branch 55 (.leaf (-2)) (.branch 56 (.leaf (-1)) (.leaf (0))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_300_5429 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (6)) (.leaf (2))) (.branch 14 (.leaf (5)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (8)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (2))) (.branch 29 (.leaf (7)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (2))) (.branch 36 (.leaf (0)) (.leaf (3))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (8)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (4)))) (.branch 43 (.branch 42 (.leaf (6)) (.leaf (2))) (.branch 44 (.leaf (5)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (7)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (4)))) (.branch 58 (.branch 57 (.leaf (6)) (.leaf (2))) (.branch 59 (.leaf (8)) (.leaf (3))))))))
  code := certificateP9_5429
  counts := ![(.branch 25 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (-6)) (.leaf (-7)))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-10)) (.leaf (-8)))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 51 (.leaf (-5)) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 57 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 54 (.branch 51 (.branch 9 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_300_5430 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (7))) (.branch 10 (.leaf (0)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (8))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (6)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (7)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (5)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (3)) (.leaf (8))) (.branch 40 (.leaf (0)) (.leaf (6)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (2)) (.leaf (4)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (7))) (.branch 51 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (6)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (8)) (.leaf (4))))))))
  code := certificateP9_5430
  counts := ![(.branch 28 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 40 (.leaf (13)) (.leaf (14))))) (.branch 52 (.branch 46 (.leaf (15)) (.branch 49 (.leaf (16)) (.leaf (17)))) (.branch 55 (.leaf (18)) (.branch 58 (.leaf (19)) (.leaf (20))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 39 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 58 (.branch 52 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 54 (.branch 51 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_300_5431 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (7)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (6))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (4))) (.branch 14 (.leaf (0)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (8)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (6)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (7)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (5)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (8)) (.leaf (3))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (6))) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (4))) (.branch 44 (.leaf (0)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (7)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (5)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (6)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (8)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (4)) (.leaf (3))))))))
  code := certificateP9_5431
  counts := ![(.branch 28 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 44 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 48 (.leaf (14)) (.leaf (15))) (.branch 54 (.leaf (16)) (.branch 58 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 55 (.leaf (-8)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 57 (.branch 48 (.leaf (-11)) (.branch 56 (.leaf (-10)) (.leaf (-8)))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 44 (.leaf (-2)) (.leaf (-1))),
  (.branch 54 (.branch 51 (.branch 34 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_300_5432 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (8)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (6)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (7)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (8)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (6)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (3)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (7)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (5)) (.leaf (0))) (.branch 44 (.leaf (3)) (.leaf (4)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (8)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (6)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (7)) (.leaf (0))) (.branch 59 (.leaf (3)) (.leaf (4))))))))
  code := certificateP9_5432
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 40 (.leaf (13)) (.leaf (14))))) (.branch 52 (.branch 46 (.leaf (15)) (.branch 50 (.leaf (16)) (.leaf (17)))) (.branch 55 (.leaf (18)) (.branch 58 (.leaf (19)) (.leaf (20))))))),
  (.branch 24 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 42 (.leaf (-17)) (.leaf (-18)))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.branch 18 (.leaf (0)) (.branch 57 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-12)) (.leaf (-13))))]
  high := ![(.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-10)) (.leaf (-8)))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-6))) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 51 (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 54 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 53 (.branch 50 (.branch 28 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_300_5433 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (7)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (6))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (8)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (2)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (6)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (3)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (4)) (.leaf (0))) (.branch 40 (.leaf (7)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (5))) (.branch 44 (.leaf (1)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (6)) (.leaf (0))) (.branch 55 (.leaf (8)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (4))) (.branch 59 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5433
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (-2))) (.branch 36 (.leaf (-3)) (.branch 51 (.leaf (-4)) (.leaf (-5))))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-8)) (.leaf (-4)))),
  (.branch 57 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 54 (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))) (.branch 55 (.leaf (-2)) (.branch 56 (.leaf (-1)) (.leaf (0))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_300_5434 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (3))) (.branch 10 (.leaf (7)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (6)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (0))) (.branch 21 (.leaf (5)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (8)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (6)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (4)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (7)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (5)) (.leaf (0)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (0))) (.branch 51 (.leaf (6)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (8)) (.leaf (4)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (3)) (.leaf (2))))))))
  code := certificateP9_5434
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-4)))) (.branch 38 (.leaf (-5)) (.branch 45 (.leaf (-6)) (.leaf (-7))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 34 (.leaf (-5)) (.leaf (-10)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 21 (.leaf (-19)) (.leaf (-23)))),
  (.branch 33 (.branch 14 (.leaf (0)) (.leaf (-8))) (.branch 51 (.leaf (-11)) (.leaf (-15)))),
  (.branch 10 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 54 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 56 (.branch 35 (.leaf (-10)) (.branch 55 (.leaf (-9)) (.leaf (-7)))) (.branch 58 (.branch 57 (.leaf (-5)) (.leaf (-3))) (.branch 59 (.leaf (-1)) (.leaf (0))))),
  (.leaf (-1)),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 22 (.leaf (-23)) (.leaf (-22))) (.branch 46 (.leaf (-21)) (.leaf (-20)))) (.branch 49 (.branch 48 (.leaf (-19)) (.leaf (-18))) (.branch 50 (.leaf (-17)) (.leaf (-16))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-15)) (.leaf (-14))) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-15)) (.leaf (-14))) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7)))))),
  (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_300_5435 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (6)) (.leaf (3))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (7))) (.branch 29 (.leaf (3)) (.leaf (0))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (1))) (.branch 36 (.leaf (4)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (5))) (.branch 44 (.leaf (2)) (.leaf (0)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (1)) (.leaf (8)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (5))) (.branch 55 (.leaf (1)) (.leaf (4)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (3)) (.leaf (1))))))))
  code := certificateP9_5435
  counts := ![(.branch 30 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 38 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.leaf (15)))))),
  (.branch 32 (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 40 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 55 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.leaf (15)))))),
  (.branch 31 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 37 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 57 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 22 (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))) (.branch 42 (.branch 35 (.leaf (-10)) (.leaf (-11))) (.branch 55 (.leaf (-15)) (.leaf (-16))))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-8)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-52))),
  (.branch 28 (.leaf (0)) (.leaf (-32))),
  (.branch 48 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 54 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 56 (.leaf (-16)) (.leaf (-14))) (.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-10)) (.leaf (-8))))),
  (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-1)),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 56 (.branch 44 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 21 (.branch 14 (.branch 11 (.branch 9 (.leaf (-52)) (.branch 10 (.leaf (-51)) (.leaf (-50)))) (.branch 12 (.leaf (-49)) (.branch 13 (.leaf (-48)) (.leaf (-47))))) (.branch 17 (.branch 15 (.leaf (-46)) (.branch 16 (.leaf (-45)) (.leaf (-44)))) (.branch 19 (.branch 18 (.leaf (-43)) (.leaf (-42))) (.branch 20 (.leaf (-41)) (.leaf (-40)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-39)) (.branch 23 (.leaf (-38)) (.leaf (-37)))) (.branch 25 (.leaf (-36)) (.branch 26 (.leaf (-35)) (.leaf (-34))))) (.branch 30 (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))) (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.leaf (-27))))))) (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.leaf (-29)))) (.branch 34 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 35 (.leaf (-26)) (.leaf (-25))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-23))) (.branch 39 (.leaf (-22)) (.leaf (-21)))) (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.leaf (-17)))))) (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_300_5436 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (4))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (1))) (.branch 10 (.leaf (6)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (8)) (.leaf (3))) (.branch 21 (.leaf (1)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (7))) (.branch 29 (.leaf (2)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (2))) (.branch 36 (.leaf (4)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (8))) (.branch 40 (.leaf (3)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (5))) (.branch 44 (.leaf (1)) (.leaf (4)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (2)) (.leaf (7)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (6))) (.branch 51 (.leaf (1)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (5))) (.branch 55 (.leaf (0)) (.leaf (4)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (2))) (.branch 59 (.leaf (8)) (.leaf (3))))))))
  code := certificateP9_5436
  counts := ![(.branch 24 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 33 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 60 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 32 (.leaf (-2)) (.branch 52 (.leaf (-3)) (.leaf (-4))))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 57 (.branch 43 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.branch 56 (.leaf (-1)) (.leaf (0))))),
  (.branch 57 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 44 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_300_5437 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (7))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (6)) (.leaf (1))) (.branch 10 (.leaf (4)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (5))) (.branch 14 (.leaf (1)) (.leaf (8)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (6)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (4))) (.branch 21 (.leaf (1)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (7)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (6))) (.branch 29 (.leaf (2)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (5)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (8))) (.branch 36 (.leaf (0)) (.leaf (3))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (6)) (.leaf (1))) (.branch 40 (.leaf (4)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (5))) (.branch 44 (.leaf (1)) (.leaf (7)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (6)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (4))) (.branch 51 (.leaf (1)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (0))) (.branch 55 (.leaf (8)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (6))) (.branch 59 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_5437
  counts := ![(.branch 24 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_300_5438 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (6))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (8)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (1))) (.branch 29 (.leaf (7)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (6)))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (0))) (.branch 36 (.leaf (2)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (8)) (.leaf (0))) (.branch 40 (.leaf (2)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (7)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (6)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (4)) (.leaf (1))) (.branch 59 (.leaf (8)) (.leaf (2))))))))
  code := certificateP9_5438
  counts := ![(.branch 26 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 44 (.branch 35 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 39 (.leaf (9)) (.leaf (10)))) (.branch 52 (.branch 47 (.leaf (11)) (.leaf (12))) (.branch 56 (.leaf (13)) (.leaf (14)))))),
  (.branch 28 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 46 (.branch 37 (.branch 32 (.leaf (7)) (.leaf (8))) (.branch 41 (.leaf (9)) (.leaf (10)))) (.branch 54 (.branch 50 (.leaf (11)) (.leaf (12))) (.branch 58 (.leaf (13)) (.leaf (14)))))),
  (.branch 30 (.branch 15 (.branch 6 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 36 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))) (.branch 17 (.leaf (-12)) (.branch 47 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.branch 32 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 57 (.branch 48 (.leaf (-15)) (.leaf (-14))) (.branch 58 (.leaf (-11)) (.branch 59 (.leaf (-8)) (.leaf (-5))))),
  (.branch 59 (.leaf (-8)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_300_5439 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (2))) (.branch 6 (.leaf (7)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (8))) (.branch 10 (.leaf (2)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (6)) (.leaf (1))) (.branch 14 (.leaf (4)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (7))) (.branch 21 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (8)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (6))) (.branch 29 (.leaf (4)) (.leaf (1))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (5)))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (1))) (.branch 36 (.leaf (7)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (8))) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (6)) (.leaf (2))) (.branch 44 (.leaf (4)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (7))) (.branch 51 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (2))) (.branch 55 (.leaf (8)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (6))) (.branch 59 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_5439
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 51 (.leaf (9)) (.branch 57 (.leaf (10)) (.leaf (11)))))),
  (.branch 32 (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 38 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 54 (.leaf (9)) (.branch 60 (.leaf (10)) (.leaf (11)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.branch 40 (.leaf (-38)) (.leaf (-40)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-10)))),
  (.branch 23 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 53 (.leaf (-17)) (.leaf (-20)))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (-9)) (.leaf (-10)))),
  (.branch 9 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.branch 41 (.leaf (-40)) (.leaf (-39))) (.branch 58 (.leaf (-33)) (.branch 59 (.leaf (-22)) (.leaf (-11))))),
  (.branch 33 (.branch 11 (.leaf (-10)) (.branch 22 (.leaf (-9)) (.leaf (-8)))) (.branch 44 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (0))))),
  (.branch 56 (.branch 54 (.leaf (-20)) (.branch 55 (.leaf (-18)) (.leaf (-16)))) (.branch 58 (.branch 57 (.leaf (-14)) (.leaf (-12))) (.branch 59 (.leaf (-10)) (.leaf (-8))))),
  (.leaf (-1)),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 43 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 40 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_300_5440 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (7))) (.branch 10 (.leaf (6)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (4))) (.branch 14 (.leaf (1)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (8)) (.leaf (1))) (.branch 21 (.leaf (6)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (0))) (.branch 29 (.leaf (7)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (6)))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (8))) (.branch 40 (.leaf (5)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (4))) (.branch 44 (.leaf (0)) (.leaf (6)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (7)) (.leaf (0))) (.branch 51 (.leaf (5)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (6)) (.leaf (1))) (.branch 59 (.leaf (8)) (.leaf (2))))))))
  code := certificateP9_5440
  counts := ![(.branch 28 (.branch 11 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 50 (.leaf (9)) (.branch 55 (.leaf (10)) (.leaf (11)))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 52 (.leaf (9)) (.branch 58 (.leaf (10)) (.leaf (11)))))),
  (.branch 30 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 36 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 32 (.leaf (-19)) (.leaf (-23)))),
  (.branch 2 (.leaf (0)) (.branch 35 (.leaf (-11)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 57 (.branch 33 (.leaf (-23)) (.branch 56 (.leaf (-22)) (.leaf (-19)))) (.branch 58 (.leaf (-16)) (.branch 59 (.leaf (-13)) (.leaf (-10))))),
  (.branch 53 (.leaf (-14)) (.branch 59 (.leaf (-13)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_300_5441 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (8))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (1))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (1))) (.branch 14 (.leaf (7)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (6)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (5))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (2))) (.branch 25 (.leaf (8)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (2)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (6)))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (7))) (.branch 36 (.leaf (2)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (3)) (.leaf (1))) (.branch 40 (.leaf (4)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (1))) (.branch 44 (.leaf (8)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (5)) (.branch 47 (.leaf (0)) (.leaf (6)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (4))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (2))) (.branch 55 (.leaf (7)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (5))) (.branch 59 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5441
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 32 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 36 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 35 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 43 (.leaf (-23)) (.leaf (-28)))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))) (.branch 54 (.branch 29 (.leaf (-4)) (.leaf (-8))) (.branch 59 (.leaf (-9)) (.leaf (-13))))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.branch 44 (.leaf (-15)) (.leaf (-16))))]
  high := ![(.branch 58 (.branch 52 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 44 (.leaf (-28)) (.leaf (-26))) (.branch 58 (.leaf (-22)) (.branch 59 (.leaf (-18)) (.leaf (-14))))),
  (.leaf (-13)),
  (.leaf (0)),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 15 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_300_5442 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (7)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (4))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (8)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (7)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (5)) (.leaf (1))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (8)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (6)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 40 (.leaf (4)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (7))) (.branch 44 (.leaf (0)) (.leaf (5)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (8))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (6)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_5442
  counts := ![(.branch 28 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 44 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 48 (.leaf (14)) (.leaf (15))) (.branch 54 (.leaf (16)) (.branch 58 (.leaf (17)) (.leaf (18))))))),
  (.branch 30 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.leaf (15)))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 36 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 27 (.branch 7 (.leaf (0)) (.leaf (-4))) (.branch 47 (.leaf (-6)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 49 (.leaf (-10)) (.leaf (-11)))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.branch 29 (.leaf (0)) (.leaf (-1))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 12 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 55 (.leaf (-8)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 48 (.leaf (-8)) (.leaf (-7))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 10 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_300_5443 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (7)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (0))) (.branch 10 (.leaf (4)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (8))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (6)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (7)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (2)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (8)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (3)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (6)) (.leaf (0))) (.branch 40 (.leaf (4)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (7))) (.branch 44 (.leaf (1)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (8)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (6))) (.branch 59 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5443
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (-2))) (.branch 36 (.leaf (-3)) (.branch 51 (.leaf (-4)) (.leaf (-5))))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-8)) (.leaf (-4)))),
  (.branch 57 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 54 (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))) (.branch 55 (.leaf (-2)) (.branch 56 (.leaf (-1)) (.leaf (0))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_300_5444 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (7)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (1))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (8)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (6))) (.branch 21 (.leaf (4)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (7))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (8)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (4)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (3)) (.leaf (1))) (.branch 40 (.leaf (6)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (0))) (.branch 44 (.leaf (7)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (0)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (4)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (8))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (6))))))))
  code := certificateP9_5444
  counts := ![(.branch 29 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 41 (.leaf (13)) (.leaf (14))))) (.branch 53 (.branch 47 (.leaf (15)) (.branch 49 (.leaf (16)) (.leaf (17)))) (.branch 55 (.leaf (18)) (.branch 59 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 32 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 32 (.leaf (-13)) (.leaf (-18)))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 48 (.leaf (-15)) (.leaf (-17)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (-5))) (.branch 46 (.leaf (-10)) (.leaf (-13)))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 14 (.leaf (0)) (.branch 33 (.leaf (-6)) (.leaf (-7))))]
  high := ![(.branch 56 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.branch 33 (.leaf (-18)) (.leaf (-17))) (.branch 59 (.leaf (-16)) (.leaf (-13)))),
  (.branch 57 (.branch 49 (.leaf (-17)) (.leaf (-16))) (.branch 58 (.leaf (-13)) (.branch 59 (.leaf (-10)) (.leaf (-7))))),
  (.branch 58 (.branch 47 (.leaf (-13)) (.leaf (-12))) (.branch 59 (.leaf (-10)) (.leaf (-8)))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 51 (.branch 47 (.branch 45 (.branch 4 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 34 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_300_5445 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (7)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (3))) (.branch 10 (.leaf (4)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (8)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (0))) (.branch 21 (.leaf (7)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (4)) (.leaf (5)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (8)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (6)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (4)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (7)) (.leaf (0)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (5)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (0))) (.branch 51 (.leaf (8)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (4)) (.leaf (6)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (3)) (.leaf (2))))))))
  code := certificateP9_5445
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-4)))) (.branch 38 (.leaf (-5)) (.branch 45 (.leaf (-6)) (.leaf (-7))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 34 (.leaf (-5)) (.leaf (-10)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 21 (.leaf (-19)) (.leaf (-23)))),
  (.branch 33 (.branch 14 (.leaf (0)) (.leaf (-8))) (.branch 51 (.leaf (-11)) (.leaf (-15))))]
  high := ![(.branch 54 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 56 (.branch 35 (.leaf (-10)) (.branch 55 (.leaf (-9)) (.leaf (-7)))) (.branch 58 (.branch 57 (.leaf (-5)) (.leaf (-3))) (.branch 59 (.leaf (-1)) (.leaf (0))))),
  (.leaf (-1)),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 22 (.leaf (-23)) (.leaf (-22))) (.branch 46 (.leaf (-21)) (.leaf (-20)))) (.branch 49 (.branch 48 (.leaf (-19)) (.leaf (-18))) (.branch 50 (.leaf (-17)) (.leaf (-16))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-15)) (.leaf (-14))) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-15)) (.leaf (-14))) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))))]
def witnessP9_300_5446 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (7)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (4)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (8))) (.branch 14 (.leaf (1)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (5)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (7)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (2)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (8)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (5)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (3)) (.leaf (0))) (.branch 40 (.leaf (4)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (7))) (.branch 44 (.leaf (1)) (.leaf (6)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (5)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (8)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_5446
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-8)) (.leaf (-4)))),
  (.branch 57 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_300_5447 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (7)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (5))) (.branch 6 (.leaf (2)) (.leaf (8))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (6)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (7))) (.branch 14 (.leaf (2)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (8)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (6))) (.branch 21 (.leaf (3)) (.leaf (7))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (8))) (.branch 29 (.leaf (3)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (7)))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (1)) (.leaf (8))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (3)) (.leaf (0))) (.branch 40 (.leaf (6)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (7))) (.branch 44 (.leaf (1)) (.leaf (5)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (8)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (6))) (.branch 51 (.leaf (4)) (.leaf (7))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (5)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (8))) (.branch 59 (.leaf (4)) (.leaf (6))))))))
  code := certificateP9_5447
  counts := ![(.branch 24 (.branch 9 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.leaf (7))))),
  (.branch 29 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.leaf (7))))),
  (.branch 34 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-20))) (.branch 27 (.leaf (-21)) (.branch 44 (.leaf (-23)) (.leaf (-24))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-8))) (.branch 57 (.leaf (-10)) (.leaf (-11)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-14))) (.branch 29 (.leaf (-16)) (.leaf (-17)))),
  (.branch 42 (.branch 8 (.leaf (0)) (.leaf (-2))) (.branch 59 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 56 (.branch 47 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-10)))) (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-6))) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 56 (.branch 54 (.branch 45 (.leaf (-24)) (.leaf (-23))) (.branch 55 (.leaf (-20)) (.leaf (-17)))) (.branch 58 (.branch 57 (.leaf (-14)) (.leaf (-11))) (.branch 59 (.leaf (-8)) (.leaf (-5))))),
  (.branch 58 (.leaf (-11)) (.branch 59 (.leaf (-8)) (.leaf (-5)))),
  (.branch 48 (.branch 30 (.leaf (-17)) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 58 (.branch 57 (.leaf (-14)) (.leaf (-11))) (.branch 59 (.leaf (-8)) (.leaf (-5))))),
  (.leaf (-5)),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_300_5448 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (7)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (3)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (8))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (6))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (7)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (5)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (8)))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (0))) (.branch 36 (.leaf (4)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (3)) (.leaf (5)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (7))) (.branch 44 (.leaf (1)) (.leaf (4)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (6)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (5))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (8)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (6)) (.leaf (3))))))))
  code := certificateP9_5448
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-8)) (.leaf (-4)))),
  (.branch 57 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_300_5449 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (7)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (4))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (1))) (.branch 10 (.leaf (6)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (1))) (.branch 14 (.leaf (4)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (8)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (6))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (2))) (.branch 25 (.leaf (4)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (2)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (7)))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (4))) (.branch 36 (.leaf (2)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (3)) (.leaf (1))) (.branch 40 (.leaf (5)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (1))) (.branch 44 (.leaf (4)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (6)) (.branch 47 (.leaf (0)) (.leaf (8)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (5))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (2))) (.branch 55 (.leaf (4)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (6))) (.branch 59 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5449
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 32 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 36 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 43 (.leaf (-23)) (.leaf (-28)))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))) (.branch 54 (.branch 29 (.leaf (-4)) (.leaf (-8))) (.branch 59 (.leaf (-9)) (.leaf (-13))))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-27))),
  (.branch 18 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 58 (.branch 52 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 44 (.leaf (-28)) (.leaf (-26))) (.branch 58 (.leaf (-22)) (.branch 59 (.leaf (-18)) (.leaf (-14))))),
  (.leaf (-13)),
  (.leaf (0)),
  (.branch 57 (.branch 45 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.branch 39 (.branch 36 (.branch 34 (.leaf (-27)) (.branch 35 (.leaf (-26)) (.leaf (-25)))) (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22))))) (.branch 42 (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19)))) (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_300_5450 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (4))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (6)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (1))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (7)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (5))) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (0))) (.branch 44 (.leaf (3)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (8))) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (5)) (.leaf (1))))))))
  code := certificateP9_5450
  counts := ![(.branch 28 (.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 23 (.leaf (9)) (.branch 26 (.leaf (10)) (.leaf (11)))))) (.branch 43 (.branch 36 (.branch 31 (.leaf (12)) (.branch 33 (.leaf (13)) (.leaf (14)))) (.branch 38 (.leaf (15)) (.branch 41 (.leaf (16)) (.leaf (17))))) (.branch 51 (.branch 46 (.leaf (18)) (.branch 48 (.leaf (19)) (.leaf (20)))) (.branch 56 (.branch 53 (.leaf (21)) (.leaf (22))) (.branch 58 (.leaf (23)) (.leaf (24))))))),
  (.branch 30 (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-46))),
  (.branch 34 (.leaf (0)) (.leaf (-26))),
  (.branch 54 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 59 (.leaf (-4)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 37 (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-46)) (.leaf (-45))) (.branch 17 (.leaf (-44)) (.branch 18 (.leaf (-43)) (.leaf (-42))))) (.branch 22 (.branch 20 (.leaf (-41)) (.branch 21 (.leaf (-40)) (.leaf (-39)))) (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36)))))) (.branch 31 (.branch 28 (.branch 26 (.leaf (-35)) (.branch 27 (.leaf (-34)) (.leaf (-33)))) (.branch 29 (.leaf (-32)) (.branch 30 (.leaf (-31)) (.leaf (-30))))) (.branch 34 (.branch 32 (.leaf (-29)) (.branch 33 (.leaf (-28)) (.leaf (-27)))) (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24))))))) (.branch 48 (.branch 42 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_300_5451 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (3))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (7))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (1)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (0))) (.branch 36 (.leaf (2)) (.leaf (4))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (3))) (.branch 40 (.leaf (0)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (3))) (.branch 44 (.leaf (0)) (.leaf (5)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (8))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (3))) (.branch 55 (.leaf (1)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (1)) (.leaf (6))))))))
  code := certificateP9_5451
  counts := ![(.branch 27 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 44 (.branch 35 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 40 (.leaf (9)) (.leaf (10)))) (.branch 53 (.branch 48 (.leaf (11)) (.leaf (12))) (.branch 57 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 55 (.branch 50 (.leaf (11)) (.leaf (12))) (.branch 59 (.leaf (13)) (.leaf (14)))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 7 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.branch 60 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-23)) (.leaf (-25)))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 50 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.leaf (0)),
  (.branch 22 (.leaf (0)) (.leaf (-38))),
  (.branch 52 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 49 (.branch 36 (.leaf (-25)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-14)) (.leaf (-7))))),
  (.branch 51 (.leaf (-6)) (.leaf (-5))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 48 (.branch 42 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 41 (.branch 31 (.branch 26 (.branch 24 (.branch 23 (.leaf (-38)) (.leaf (-37))) (.branch 25 (.leaf (-36)) (.leaf (-35)))) (.branch 28 (.branch 27 (.leaf (-34)) (.leaf (-33))) (.branch 29 (.leaf (-32)) (.branch 30 (.leaf (-31)) (.leaf (-30)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-29)) (.leaf (-28))) (.branch 34 (.leaf (-27)) (.branch 35 (.leaf (-26)) (.leaf (-25))))) (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-23))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))))) (.branch 50 (.branch 45 (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_300_5452 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (0))) (.branch 10 (.leaf (5)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (6)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (8)) (.leaf (0))) (.branch 21 (.leaf (5)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (1)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (7)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (0))) (.branch 36 (.leaf (4)) (.leaf (6))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (8)) (.leaf (0))) (.branch 40 (.leaf (5)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (0))) (.branch 44 (.leaf (3)) (.leaf (4)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (6)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (7)) (.leaf (0))) (.branch 51 (.leaf (5)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (3))) (.branch 55 (.leaf (1)) (.leaf (4)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (6))) (.branch 59 (.leaf (8)) (.leaf (5))))))))
  code := certificateP9_5452
  counts := ![(.branch 27 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 2 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 16 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 23 (.leaf (-15)) (.branch 53 (.leaf (-18)) (.leaf (-20))))),
  (.branch 3 (.leaf (0)) (.branch 25 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 58 (.branch 54 (.leaf (-20)) (.leaf (-19))) (.branch 59 (.leaf (-14)) (.leaf (-9)))),
  (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 57 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 48 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 54 (.branch 51 (.branch 9 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_300_5453 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (3))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (7))) (.branch 21 (.leaf (0)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (1))) (.branch 29 (.leaf (4)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (3))) (.branch 40 (.leaf (8)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (5))) (.branch 51 (.leaf (0)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (4))) (.branch 55 (.leaf (2)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (4)) (.leaf (6))))))))
  code := certificateP9_5453
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 34 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 60 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 20 (.leaf (0)) (.leaf (-40))),
  (.branch 40 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 40 (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-40)) (.leaf (-39))) (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36))))) (.branch 27 (.branch 26 (.leaf (-35)) (.leaf (-34))) (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-27)) (.leaf (-26))))) (.branch 37 (.branch 36 (.leaf (-25)) (.leaf (-24))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))))) (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_300_5454 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (0))) (.branch 10 (.leaf (6)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (4))) (.branch 14 (.leaf (0)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (8)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (1))) (.branch 25 (.leaf (6)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (7))) (.branch 29 (.leaf (1)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (0))) (.branch 36 (.leaf (3)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (8)) (.leaf (0))) (.branch 40 (.leaf (6)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (4))) (.branch 44 (.leaf (0)) (.leaf (5)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (3)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (7)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (1))) (.branch 55 (.leaf (6)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (8))) (.branch 59 (.leaf (1)) (.leaf (5))))))))
  code := certificateP9_5454
  counts := ![(.branch 27 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 44 (.branch 35 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 39 (.leaf (9)) (.leaf (10)))) (.branch 52 (.branch 48 (.leaf (11)) (.leaf (12))) (.branch 57 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 54 (.branch 50 (.leaf (11)) (.leaf (12))) (.branch 59 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-23))) (.branch 9 (.leaf (-25)) (.leaf (-27)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 24 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-6)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 53 (.branch 40 (.leaf (-27)) (.leaf (-26))) (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-14)) (.leaf (-7))))),
  (.branch 55 (.leaf (-12)) (.leaf (-7))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 29 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_300_5455 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (7)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (8))) (.branch 21 (.leaf (0)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (5))) (.branch 25 (.leaf (4)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (7)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (5))) (.branch 36 (.leaf (2)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (8)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (1))) (.branch 44 (.leaf (5)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (6)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (4))) (.branch 51 (.leaf (1)) (.leaf (7))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (0))) (.branch 55 (.leaf (5)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (4)) (.leaf (8))))))))
  code := certificateP9_5455
  counts := ![(.branch 29 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.leaf (15)))))),
  (.branch 31 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 37 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 57 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 43 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-46)) (.leaf (-50)))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-25))) (.branch 30 (.leaf (-29)) (.leaf (-30)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (-4))) (.branch 33 (.leaf (-8)) (.branch 50 (.leaf (-9)) (.leaf (-10))))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 50 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-5)) (.leaf (-4)))),
  (.branch 56 (.branch 54 (.branch 11 (.leaf (-50)) (.leaf (-49))) (.branch 55 (.leaf (-42)) (.leaf (-35)))) (.branch 58 (.branch 57 (.leaf (-28)) (.leaf (-21))) (.branch 59 (.leaf (-14)) (.leaf (-7))))),
  (.branch 57 (.branch 31 (.leaf (-30)) (.leaf (-28))) (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-14)) (.leaf (-7))))),
  (.branch 51 (.leaf (-10)) (.leaf (-7))),
  (.branch 57 (.branch 45 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessP9_300_5456 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (4))) (.branch 6 (.leaf (7)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (8)) (.branch 17 (.leaf (3)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (4))) (.branch 21 (.leaf (1)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (7)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (6))) (.branch 29 (.leaf (4)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (4))) (.branch 36 (.leaf (8)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (3)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (6)))) (.branch 43 (.branch 42 (.leaf (5)) (.leaf (0))) (.branch 44 (.leaf (4)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (7)) (.branch 47 (.leaf (3)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (4))) (.branch 51 (.leaf (1)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (8)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (6))) (.branch 59 (.leaf (4)) (.leaf (3))))))))
  code := certificateP9_5456
  counts := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 33 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 24 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 54 (.leaf (-20)) (.leaf (-22)))),
  (.branch 22 (.leaf (0)) (.branch 52 (.leaf (-2)) (.leaf (-4)))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 35 (.leaf (-4)) (.branch 50 (.leaf (-5)) (.leaf (-6))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 42 (.leaf (-18)) (.leaf (-21)))),
  (.branch 11 (.leaf (0)) (.branch 41 (.leaf (-5)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 55 (.leaf (-22)) (.branch 56 (.leaf (-19)) (.leaf (-16)))) (.branch 58 (.leaf (-13)) (.branch 59 (.leaf (-10)) (.leaf (-7))))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.branch 56 (.leaf (-1)) (.leaf (0))))),
  (.branch 51 (.leaf (-6)) (.leaf (-5))),
  (.branch 56 (.branch 54 (.branch 43 (.leaf (-21)) (.leaf (-20))) (.branch 55 (.leaf (-18)) (.leaf (-16)))) (.branch 58 (.branch 57 (.leaf (-14)) (.leaf (-12))) (.branch 59 (.leaf (-10)) (.leaf (-8))))),
  (.branch 42 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))),
  (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_300_5457 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (8))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (7)))) (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (2)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (8))) (.branch 21 (.leaf (1)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (7)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (4))) (.branch 29 (.leaf (6)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (8)) (.leaf (5))) (.branch 36 (.leaf (3)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (4)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (7)))) (.branch 43 (.branch 42 (.leaf (6)) (.leaf (0))) (.branch 44 (.leaf (3)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (5)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (8))) (.branch 51 (.leaf (1)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (6)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (7)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (4))) (.branch 59 (.leaf (3)) (.leaf (5))))))))
  code := certificateP9_5457
  counts := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 33 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 12 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 17 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 24 (.leaf (-18)) (.branch 46 (.leaf (-20)) (.leaf (-23))))),
  (.branch 6 (.leaf (0)) (.branch 36 (.leaf (-5)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 23 (.leaf (0)) (.leaf (-1))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-17))) (.branch 53 (.leaf (-18)) (.leaf (-19)))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.branch 34 (.leaf (-10)) (.leaf (-11))))]
  high := ![(.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 56 (.branch 47 (.leaf (-23)) (.branch 55 (.leaf (-22)) (.leaf (-19)))) (.branch 58 (.branch 57 (.leaf (-16)) (.leaf (-13))) (.branch 59 (.leaf (-10)) (.leaf (-7))))),
  (.leaf (-7)),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 48 (.leaf (-1)) (.leaf (0))),
  (.branch 56 (.branch 54 (.leaf (-19)) (.branch 55 (.leaf (-17)) (.leaf (-15)))) (.branch 58 (.branch 57 (.leaf (-13)) (.leaf (-11))) (.branch 59 (.leaf (-9)) (.leaf (-7))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 54 (.branch 51 (.branch 35 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_300_5458 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (8)) (.leaf (1))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (7)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (5))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (8)) (.leaf (4))) (.branch 29 (.leaf (1)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (5))) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (7)) (.leaf (1))) (.branch 40 (.leaf (4)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (3)) (.leaf (2))) (.branch 44 (.leaf (1)) (.leaf (6)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (5)) (.leaf (8)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (4))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (7)) (.leaf (5))) (.branch 59 (.leaf (1)) (.leaf (6))))))))
  code := certificateP9_5458
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 32 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 18 (.leaf (0)) (.branch 57 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-12)) (.leaf (-13))))]
  high := ![(.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 54 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 53 (.branch 50 (.branch 28 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_300_5459 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (1))) (.branch 6 (.leaf (8)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (2))) (.branch 10 (.leaf (6)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (7)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (6)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (5))) (.branch 29 (.leaf (1)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (1))) (.branch 36 (.leaf (8)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (4)) (.leaf (2))) (.branch 40 (.leaf (5)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (2)) (.leaf (4)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (6)) (.branch 47 (.leaf (1)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (7)) (.leaf (4))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (6))) (.branch 59 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_5459
  counts := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 22 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 21 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-24)))]
  high := ![(.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 58 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 56 (.branch 54 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 48 (.branch 42 (.branch 39 (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22)))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_300_5460 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (8))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (2))) (.branch 10 (.leaf (6)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (7)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (1)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (8)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (6))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (7)) (.leaf (5))) (.branch 29 (.leaf (4)) (.leaf (1))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (8))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (4)) (.leaf (2))) (.branch 40 (.leaf (5)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (7)) (.leaf (3))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (6)) (.branch 47 (.leaf (1)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (8)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (5))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (7)) (.leaf (6))) (.branch 59 (.leaf (4)) (.leaf (1))))))))
  code := certificateP9_5460
  counts := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 36 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 32 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-10)) (.leaf (-11))))]
  high := ![(.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 48 (.leaf (-1)) (.leaf (0))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.leaf (-2)) (.leaf (-1))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_300_5461 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (6))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (8))) (.branch 10 (.leaf (2)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (1)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (7)) (.branch 17 (.leaf (2)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (5))) (.branch 21 (.leaf (1)) (.leaf (8))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (6)))) (.branch 28 (.branch 27 (.leaf (7)) (.leaf (4))) (.branch 29 (.leaf (1)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (8)) (.leaf (6))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (4)) (.leaf (7))) (.branch 40 (.leaf (2)) (.leaf (5)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (3))) (.branch 44 (.leaf (1)) (.leaf (6)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (8)) (.branch 47 (.leaf (2)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (1)) (.leaf (7))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (6)))) (.branch 58 (.branch 57 (.leaf (8)) (.leaf (4))) (.branch 59 (.leaf (1)) (.leaf (5))))))))
  code := certificateP9_5461
  counts := ![(.branch 24 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 11 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-8)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.leaf (-3)) (.leaf (-2))),
  (.branch 57 (.branch 48 (.leaf (-11)) (.branch 56 (.leaf (-10)) (.leaf (-8)))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 57 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 53 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_300_5462 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (1))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (7)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (6)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (3))) (.branch 29 (.leaf (1)) (.leaf (8))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (3))) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (6)) (.leaf (1))) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (2))) (.branch 44 (.leaf (1)) (.leaf (7)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (6)) (.leaf (3))) (.branch 59 (.leaf (1)) (.leaf (8))))))))
  code := certificateP9_5462
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 32 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 35 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.branch 60 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-12)) (.leaf (-13)))),
  (.branch 18 (.leaf (0)) (.branch 57 (.leaf (-2)) (.leaf (-3)))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 56 (.branch 54 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 50 (.branch 28 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_300_5463 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (1))) (.branch 10 (.leaf (7)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (6))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (8))) (.branch 21 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (1))) (.branch 25 (.leaf (3)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (6))) (.branch 29 (.leaf (1)) (.leaf (7))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (3))) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (5)) (.leaf (1))) (.branch 40 (.leaf (8)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (6))) (.branch 44 (.leaf (1)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (7))) (.branch 51 (.leaf (0)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (1))) (.branch 55 (.leaf (3)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (6))) (.branch 59 (.leaf (1)) (.leaf (8))))))))
  code := certificateP9_5463
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_300_5464 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (2))) (.branch 10 (.leaf (7)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (1))) (.branch 14 (.leaf (6)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (8))) (.branch 21 (.leaf (0)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (2))) (.branch 25 (.leaf (3)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (1))) (.branch 29 (.leaf (6)) (.leaf (7))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (3))) (.branch 36 (.leaf (0)) (.leaf (5))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (2))) (.branch 40 (.leaf (8)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (1))) (.branch 44 (.leaf (6)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (7))) (.branch 51 (.leaf (0)) (.leaf (4))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (2))) (.branch 55 (.leaf (3)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (5)) (.leaf (1))) (.branch 59 (.leaf (6)) (.leaf (8))))))))
  code := certificateP9_5464
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 34 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-10)) (.leaf (-8)))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_300 : Fin 50 → CycleWitness 9 := ![witnessP9_300_5415, witnessP9_300_5416, witnessP9_300_5417, witnessP9_300_5418, witnessP9_300_5419, witnessP9_300_5420, witnessP9_300_5421, witnessP9_300_5422, witnessP9_300_5423, witnessP9_300_5424, witnessP9_300_5425, witnessP9_300_5426, witnessP9_300_5427, witnessP9_300_5428, witnessP9_300_5429, witnessP9_300_5430, witnessP9_300_5431, witnessP9_300_5432, witnessP9_300_5433, witnessP9_300_5434, witnessP9_300_5435, witnessP9_300_5436, witnessP9_300_5437, witnessP9_300_5438, witnessP9_300_5439, witnessP9_300_5440, witnessP9_300_5441, witnessP9_300_5442, witnessP9_300_5443, witnessP9_300_5444, witnessP9_300_5445, witnessP9_300_5446, witnessP9_300_5447, witnessP9_300_5448, witnessP9_300_5449, witnessP9_300_5450, witnessP9_300_5451, witnessP9_300_5452, witnessP9_300_5453, witnessP9_300_5454, witnessP9_300_5455, witnessP9_300_5456, witnessP9_300_5457, witnessP9_300_5458, witnessP9_300_5459, witnessP9_300_5460, witnessP9_300_5461, witnessP9_300_5462, witnessP9_300_5463, witnessP9_300_5464]
end RealPinwheel.FiveSixths


