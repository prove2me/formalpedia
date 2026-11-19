-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_288
-- name    : RealPinwheel_FiveSixths_WitnessP9_288
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:17:58.089118+00:00
-- url     : https://prove2.me/theorems/b4c9252f-e10b-4a5b-ad41-e127eab49a52
-- title:
--   Exact witness block P9_288
-- statement:
--   These exact witnesses represent words 4852 through 4895 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 4852–4895; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_288_4851 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (5)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (6))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (8))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (5)) (.leaf (2))) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (7))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (5))) (.branch 28 (.leaf (3)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (6))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (2)) (.leaf (8)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (4)) (.leaf (7))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (1)) (.leaf (0))) (.branch 45 (.leaf (3)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (8))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (4)) (.leaf (2))) (.branch 54 (.leaf (3)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (5)) (.leaf (1))) (.branch 58 (.leaf (0)) (.leaf (7))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (2)) (.leaf (4))) (.branch 62 (.leaf (3)) (.leaf (1)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (6))) (.branch 66 (.leaf (5)) (.branch 67 (.leaf (2)) (.leaf (8)))))))))
  code := certificateP9_4851
  counts := ![(.branch 30 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 39 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 55 (.leaf (11)) (.leaf (12))) (.branch 64 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 36 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 40 (.leaf (5)) (.branch 46 (.leaf (6)) (.leaf (7)))) (.branch 60 (.leaf (8)) (.branch 67 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.leaf (7))))),
  (.branch 38 (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 47 (.leaf (4)) (.leaf (5))) (.branch 66 (.leaf (6)) (.leaf (7))))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.branch 68 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 24 (.leaf (-5)) (.branch 58 (.leaf (-6)) (.leaf (-7))))),
  (.branch 2 (.leaf (0)) (.branch 29 (.leaf (-24)) (.leaf (-25)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-4)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-6))) (.branch 22 (.leaf (-7)) (.branch 41 (.leaf (-8)) (.leaf (-9))))),
  (.branch 7 (.leaf (0)) (.branch 56 (.leaf (-3)) (.leaf (-4)))),
  (.branch 14 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 65 (.branch 59 (.leaf (-7)) (.leaf (-6))) (.branch 66 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3))))),
  (.branch 65 (.branch 64 (.leaf (-25)) (.leaf (-20))) (.branch 66 (.leaf (-15)) (.branch 67 (.leaf (-10)) (.leaf (-5))))),
  (.branch 54 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))),
  (.branch 65 (.branch 63 (.leaf (-12)) (.branch 64 (.leaf (-10)) (.leaf (-8)))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 64 (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-8)) (.leaf (-7)))) (.branch 66 (.branch 65 (.leaf (-6)) (.leaf (-5))) (.branch 67 (.leaf (-4)) (.leaf (-3))))),
  (.branch 67 (.leaf (-4)) (.leaf (-3))),
  (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_288_4852 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (8)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (6)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (7)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (5))) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (6))) (.branch 24 (.leaf (8)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (4)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (5)) (.leaf (0))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (7)) (.leaf (6)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (3)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (8)) (.leaf (5))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (2)) (.leaf (0))) (.branch 45 (.leaf (6)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (4)) (.branch 50 (.leaf (7)) (.leaf (2))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (5))) (.branch 54 (.leaf (3)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (6))) (.branch 58 (.leaf (8)) (.leaf (2))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (4)) (.leaf (0))) (.branch 62 (.leaf (1)) (.leaf (3)))) (.branch 65 (.branch 64 (.leaf (5)) (.leaf (0))) (.branch 66 (.leaf (2)) (.branch 67 (.leaf (7)) (.leaf (6)))))))))
  code := certificateP9_4852
  counts := ![(.branch 31 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 48 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 61 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 32 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 59 (.leaf (7)) (.branch 66 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 67 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-50)) (.leaf (-55)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-14))) (.branch 28 (.leaf (-19)) (.branch 43 (.leaf (-20)) (.leaf (-21))))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-22))) (.branch 26 (.leaf (-23)) (.leaf (-24)))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (-10))) (.branch 30 (.leaf (-11)) (.leaf (-12)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 16 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 66 (.branch 57 (.leaf (-14)) (.leaf (-12))) (.branch 67 (.leaf (-8)) (.leaf (-4)))),
  (.branch 64 (.branch 10 (.leaf (-55)) (.branch 63 (.leaf (-54)) (.leaf (-45)))) (.branch 66 (.branch 65 (.leaf (-36)) (.leaf (-27))) (.branch 67 (.leaf (-18)) (.leaf (-9))))),
  (.branch 44 (.leaf (-21)) (.branch 67 (.leaf (-18)) (.leaf (-9)))),
  (.branch 65 (.branch 55 (.leaf (-11)) (.branch 64 (.leaf (-10)) (.leaf (-8)))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 64 (.branch 62 (.branch 61 (.leaf (-24)) (.leaf (-21))) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3)))),
  (.branch 46 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_288_4853 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (5))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (4))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (7)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (5))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (4)) (.leaf (2)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (1)) (.leaf (4))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (6)) (.leaf (0))) (.branch 45 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (5))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (4)) (.leaf (2))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (1)) (.leaf (0))) (.branch 54 (.leaf (3)) (.leaf (5)))) (.branch 57 (.branch 56 (.leaf (1)) (.leaf (2))) (.branch 58 (.leaf (0)) (.leaf (4))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (8)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (5))) (.branch 66 (.leaf (1)) (.branch 67 (.leaf (4)) (.leaf (2)))))))))
  code := certificateP9_4853
  counts := ![(.branch 30 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 39 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 64 (.leaf (13)) (.leaf (14)))))),
  (.branch 32 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))) (.branch 52 (.branch 41 (.branch 36 (.leaf (7)) (.leaf (8))) (.branch 47 (.leaf (9)) (.leaf (10)))) (.branch 61 (.branch 56 (.leaf (11)) (.leaf (12))) (.branch 66 (.leaf (13)) (.leaf (14)))))),
  (.branch 34 (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 40 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 57 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 67 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 60 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 19 (.leaf (-5)) (.branch 53 (.leaf (-6)) (.leaf (-7))))),
  (.branch 2 (.leaf (0)) (.branch 36 (.leaf (-3)) (.leaf (-4)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 38 (.leaf (-6)) (.branch 55 (.leaf (-7)) (.leaf (-8))))),
  (.branch 9 (.leaf (0)) (.leaf (-25))),
  (.branch 26 (.leaf (0)) (.leaf (-42))),
  (.branch 60 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 65 (.branch 59 (.leaf (-7)) (.leaf (-6))) (.branch 66 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3))))),
  (.branch 67 (.leaf (-4)) (.leaf (-3))),
  (.branch 63 (.leaf (-1)) (.leaf (0))),
  (.branch 65 (.branch 55 (.leaf (-11)) (.branch 64 (.leaf (-10)) (.leaf (-8)))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 66 (.branch 56 (.leaf (-8)) (.leaf (-7))) (.branch 67 (.leaf (-6)) (.leaf (-5)))),
  (.branch 55 (.branch 49 (.branch 46 (.branch 44 (.leaf (-25)) (.branch 45 (.leaf (-24)) (.leaf (-23)))) (.branch 47 (.leaf (-22)) (.branch 48 (.leaf (-21)) (.leaf (-20))))) (.branch 52 (.branch 50 (.leaf (-19)) (.branch 51 (.leaf (-18)) (.leaf (-17)))) (.branch 53 (.leaf (-16)) (.branch 54 (.leaf (-15)) (.leaf (-14)))))) (.branch 61 (.branch 58 (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))) (.branch 59 (.leaf (-10)) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 47 (.branch 36 (.branch 31 (.branch 28 (.branch 27 (.leaf (-42)) (.leaf (-41))) (.branch 29 (.leaf (-40)) (.branch 30 (.leaf (-39)) (.leaf (-38))))) (.branch 33 (.branch 32 (.leaf (-37)) (.leaf (-36))) (.branch 34 (.leaf (-35)) (.branch 35 (.leaf (-34)) (.leaf (-33)))))) (.branch 41 (.branch 38 (.branch 37 (.leaf (-32)) (.leaf (-31))) (.branch 39 (.leaf (-30)) (.branch 40 (.leaf (-29)) (.leaf (-28))))) (.branch 44 (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-26)) (.leaf (-25)))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-23)) (.leaf (-22))))))) (.branch 57 (.branch 52 (.branch 49 (.branch 48 (.leaf (-21)) (.leaf (-20))) (.branch 50 (.leaf (-19)) (.branch 51 (.leaf (-18)) (.leaf (-17))))) (.branch 54 (.branch 53 (.leaf (-16)) (.leaf (-15))) (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))))) (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 64 (.branch 62 (.branch 61 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_288_4854 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (7))) (.branch 7 (.leaf (2)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (6)) (.leaf (8)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (2))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (5))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (7))) (.branch 20 (.leaf (0)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (8)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (7)) (.leaf (6)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (4)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (8))) (.branch 41 (.leaf (2)) (.leaf (3))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (1)) (.leaf (0))) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 48 (.branch 47 (.leaf (4)) (.leaf (2))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (5))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (3)) (.leaf (8))) (.branch 54 (.leaf (0)) (.leaf (6)))) (.branch 57 (.branch 56 (.leaf (4)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (0))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (7)) (.leaf (3))) (.branch 62 (.leaf (5)) (.leaf (1)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (2))) (.branch 66 (.leaf (4)) (.branch 67 (.leaf (8)) (.leaf (6)))))))))
  code := certificateP9_4854
  counts := ![(.branch 30 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 39 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 59 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 64 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 36 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.leaf (7))))),
  (.branch 37 (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 47 (.leaf (4)) (.leaf (5))) (.branch 66 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 11 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 40 (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 53 (.leaf (3)) (.branch 67 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-27)) (.leaf (-33)))),
  (.branch 2 (.leaf (0)) (.branch 29 (.leaf (-24)) (.leaf (-25)))),
  (.branch 31 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-2)) (.leaf (-4)))) (.branch 48 (.leaf (-5)) (.branch 65 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-47)) (.leaf (-50)))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (-12))) (.branch 56 (.leaf (-15)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.branch 38 (.leaf (-8)) (.leaf (-10)))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (-1))) (.branch 55 (.leaf (-3)) (.leaf (-5)))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (-38))) (.branch 46 (.leaf (-41)) (.leaf (-42)))),
  (.branch 12 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 55 (.branch 45 (.branch 40 (.leaf (-33)) (.leaf (-32))) (.branch 50 (.leaf (-31)) (.leaf (-30)))) (.branch 65 (.branch 60 (.leaf (-29)) (.leaf (-28))) (.branch 66 (.leaf (-21)) (.branch 67 (.leaf (-14)) (.leaf (-7)))))),
  (.branch 65 (.branch 64 (.leaf (-25)) (.leaf (-20))) (.branch 66 (.leaf (-15)) (.branch 67 (.leaf (-10)) (.leaf (-5))))),
  (.branch 66 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5)))),
  (.branch 64 (.branch 62 (.branch 23 (.leaf (-50)) (.leaf (-49))) (.branch 63 (.leaf (-42)) (.leaf (-35)))) (.branch 66 (.branch 65 (.leaf (-28)) (.leaf (-21))) (.branch 67 (.leaf (-14)) (.leaf (-7))))),
  (.branch 57 (.leaf (-16)) (.branch 67 (.leaf (-14)) (.leaf (-7)))),
  (.branch 65 (.branch 63 (.leaf (-10)) (.branch 64 (.leaf (-9)) (.leaf (-8)))) (.branch 66 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5))))),
  (.branch 58 (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))) (.branch 59 (.leaf (-2)) (.branch 60 (.leaf (-1)) (.leaf (0))))),
  (.branch 63 (.branch 61 (.branch 47 (.leaf (-42)) (.leaf (-40))) (.branch 62 (.leaf (-35)) (.leaf (-30)))) (.branch 65 (.branch 64 (.leaf (-25)) (.leaf (-20))) (.branch 66 (.leaf (-15)) (.branch 67 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 13 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-5))))]
def witnessP9_288_4855 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (4))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (5)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (4)) (.leaf (7)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (4)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (4)) (.leaf (1))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (2)) (.leaf (3))) (.branch 45 (.leaf (0)) (.leaf (6)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (4))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (2)) (.leaf (3))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (5)) (.leaf (4)))) (.branch 57 (.branch 56 (.leaf (2)) (.leaf (0))) (.branch 58 (.leaf (3)) (.leaf (1))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (2)) (.leaf (0))) (.branch 62 (.leaf (4)) (.leaf (8)))) (.branch 65 (.branch 64 (.leaf (3)) (.leaf (1))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (2)) (.leaf (4)))))))))
  code := certificateP9_4855
  counts := ![(.branch 32 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 49 (.branch 40 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 45 (.leaf (10)) (.leaf (11)))) (.branch 57 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 61 (.leaf (14)) (.branch 66 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 16 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 39 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 67 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 34 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 55 (.branch 41 (.leaf (5)) (.branch 48 (.leaf (6)) (.leaf (7)))) (.branch 62 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 63 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 35 (.leaf (-9)) (.branch 52 (.leaf (-11)) (.leaf (-13))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (-1)) (.leaf (-3)))) (.branch 43 (.leaf (-4)) (.branch 60 (.leaf (-5)) (.leaf (-6))))),
  (.branch 3 (.leaf (0)) (.branch 30 (.leaf (-19)) (.leaf (-20)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-13)) (.leaf (-14)))),
  (.branch 12 (.leaf (0)) (.leaf (-22))),
  (.branch 29 (.leaf (0)) (.leaf (-39))),
  (.branch 63 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 62 (.leaf (-13)) (.branch 67 (.leaf (-12)) (.leaf (-10)))),
  (.branch 60 (.branch 48 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.leaf (-6)) (.leaf (-5))),
  (.branch 66 (.branch 65 (.leaf (-20)) (.leaf (-15))) (.branch 67 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 61 (.branch 57 (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 51 (.branch 48 (.branch 47 (.leaf (-22)) (.leaf (-21))) (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-19)) (.leaf (-18))))) (.branch 54 (.branch 52 (.leaf (-17)) (.branch 53 (.leaf (-16)) (.leaf (-15)))) (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))))) (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 38 (.branch 33 (.branch 31 (.branch 30 (.leaf (-39)) (.leaf (-38))) (.branch 32 (.leaf (-37)) (.leaf (-36)))) (.branch 35 (.branch 34 (.leaf (-35)) (.leaf (-34))) (.branch 36 (.leaf (-33)) (.branch 37 (.leaf (-32)) (.leaf (-31)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-30)) (.leaf (-29))) (.branch 41 (.leaf (-28)) (.branch 42 (.leaf (-27)) (.leaf (-26))))) (.branch 45 (.branch 44 (.leaf (-25)) (.leaf (-24))) (.branch 46 (.leaf (-23)) (.branch 47 (.leaf (-22)) (.leaf (-21))))))) (.branch 58 (.branch 53 (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-19))) (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-17)) (.leaf (-16))))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-14))) (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))))) (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_288_4856 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (8)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (7)) (.leaf (6))) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (1)) (.leaf (4))) (.branch 28 (.leaf (0)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (3))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (0)) (.leaf (8)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (4)) (.leaf (6)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (3)) (.leaf (1))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (5)) (.leaf (0))) (.branch 45 (.leaf (2)) (.leaf (7)))) (.branch 48 (.branch 47 (.leaf (4)) (.leaf (1))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (6)) (.leaf (3))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (2)) (.leaf (0))) (.branch 54 (.leaf (1)) (.leaf (4)))) (.branch 57 (.branch 56 (.leaf (8)) (.leaf (5))) (.branch 58 (.leaf (0)) (.leaf (2))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (1)) (.leaf (3))) (.branch 62 (.leaf (0)) (.leaf (6)))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (4))) (.branch 66 (.leaf (2)) (.branch 67 (.leaf (0)) (.leaf (7)))))))))
  code := certificateP9_4856
  counts := ![(.branch 33 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 49 (.branch 40 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 58 (.branch 53 (.leaf (12)) (.leaf (13))) (.branch 62 (.leaf (14)) (.branch 67 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 39 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.leaf (7))))),
  (.branch 37 (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 55 (.branch 47 (.leaf (4)) (.leaf (5))) (.branch 65 (.leaf (6)) (.leaf (7))))),
  (.branch 29 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 46 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 68 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 35 (.leaf (-24)) (.leaf (-34)))),
  (.branch 30 (.branch 2 (.leaf (0)) (.leaf (-19))) (.branch 64 (.leaf (-24)) (.leaf (-28)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-9)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.branch 21 (.leaf (-41)) (.leaf (-51)))),
  (.branch 7 (.leaf (0)) (.branch 55 (.leaf (-17)) (.leaf (-24)))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 29 (.leaf (-12)) (.leaf (-13)))),
  (.branch 50 (.branch 9 (.leaf (0)) (.leaf (-5))) (.branch 63 (.leaf (-6)) (.leaf (-7)))),
  (.branch 22 (.leaf (0)) (.leaf (-1))),
  (.branch 34 (.branch 12 (.leaf (0)) (.leaf (-11))) (.branch 56 (.leaf (-12)) (.leaf (-13))))]
  high := ![(.branch 45 (.branch 36 (.leaf (-34)) (.leaf (-33))) (.branch 54 (.leaf (-32)) (.branch 63 (.leaf (-31)) (.leaf (-27))))),
  (.branch 66 (.branch 65 (.leaf (-28)) (.leaf (-23))) (.branch 67 (.leaf (-18)) (.leaf (-13)))),
  (.branch 53 (.branch 46 (.leaf (-13)) (.leaf (-12))) (.branch 60 (.leaf (-11)) (.branch 67 (.leaf (-10)) (.leaf (-5))))),
  (.branch 62 (.branch 32 (.branch 22 (.leaf (-51)) (.leaf (-50))) (.branch 42 (.leaf (-49)) (.branch 52 (.leaf (-48)) (.leaf (-47))))) (.branch 65 (.branch 63 (.leaf (-41)) (.branch 64 (.leaf (-35)) (.leaf (-29)))) (.branch 66 (.leaf (-23)) (.branch 67 (.leaf (-17)) (.leaf (-11)))))),
  (.branch 66 (.branch 56 (.leaf (-24)) (.leaf (-23))) (.branch 67 (.leaf (-17)) (.leaf (-11)))),
  (.branch 62 (.branch 59 (.branch 58 (.leaf (-13)) (.leaf (-12))) (.branch 60 (.leaf (-11)) (.branch 61 (.leaf (-10)) (.leaf (-9))))) (.branch 65 (.branch 63 (.leaf (-8)) (.branch 64 (.leaf (-7)) (.leaf (-6)))) (.branch 66 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 65 (.branch 64 (.leaf (-7)) (.leaf (-6))) (.branch 66 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3))))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 62 (.branch 59 (.branch 57 (.leaf (-13)) (.branch 58 (.leaf (-12)) (.leaf (-11)))) (.branch 60 (.leaf (-10)) (.branch 61 (.leaf (-9)) (.leaf (-8))))) (.branch 65 (.branch 63 (.leaf (-7)) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.leaf (-4)) (.branch 67 (.leaf (-3)) (.leaf (-2))))))]
def witnessP9_288_4857 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (7)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (6))) (.branch 11 (.leaf (3)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (8))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (4)) (.leaf (5))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (3)) (.leaf (7)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (6)) (.leaf (4))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (8))) (.branch 28 (.leaf (3)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (5))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (4)) (.leaf (7)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (6)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (8)) (.leaf (4))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (1)) (.leaf (5))) (.branch 45 (.leaf (3)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (7))) (.branch 49 (.leaf (1)) (.branch 50 (.leaf (4)) (.leaf (6))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (2))) (.branch 54 (.leaf (3)) (.leaf (8)))) (.branch 57 (.branch 56 (.leaf (1)) (.leaf (0))) (.branch 58 (.leaf (5)) (.leaf (4))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (2)) (.leaf (7))) (.branch 62 (.leaf (3)) (.leaf (1)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (6))) (.branch 66 (.leaf (2)) (.branch 67 (.leaf (4)) (.leaf (8)))))))))
  code := certificateP9_4857
  counts := ![(.branch 30 (.branch 13 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 36 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 39 (.leaf (5)) (.branch 46 (.leaf (6)) (.leaf (7)))) (.branch 60 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 67 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 65 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 61 (.leaf (4)) (.leaf (5))))),
  (.branch 41 (.branch 14 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 55 (.leaf (3)) (.branch 68 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 23 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))) (.branch 40 (.leaf (-7)) (.branch 57 (.leaf (-8)) (.leaf (-9))))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-24)) (.leaf (-27)))),
  (.branch 5 (.leaf (0)) (.branch 32 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (-48))) (.branch 44 (.leaf (-51)) (.leaf (-52)))),
  (.branch 10 (.leaf (0)) (.leaf (-18))),
  (.branch 34 (.branch 7 (.leaf (0)) (.leaf (-33))) (.branch 61 (.leaf (-34)) (.leaf (-35)))),
  (.branch 27 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 65 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 66 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5))))),
  (.branch 64 (.branch 50 (.leaf (-27)) (.branch 57 (.leaf (-26)) (.leaf (-25)))) (.branch 66 (.branch 65 (.leaf (-20)) (.leaf (-15))) (.branch 67 (.leaf (-10)) (.leaf (-5))))),
  (.branch 67 (.leaf (-10)) (.leaf (-5))),
  (.branch 65 (.branch 63 (.leaf (-12)) (.branch 64 (.leaf (-10)) (.leaf (-8)))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 62 (.branch 59 (.branch 45 (.leaf (-52)) (.leaf (-50))) (.branch 60 (.leaf (-45)) (.branch 61 (.leaf (-40)) (.leaf (-35))))) (.branch 65 (.branch 63 (.leaf (-30)) (.branch 64 (.leaf (-25)) (.leaf (-20)))) (.branch 66 (.leaf (-15)) (.branch 67 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 52 (.branch 11 (.leaf (-18)) (.leaf (-17))) (.branch 66 (.leaf (-15)) (.branch 67 (.leaf (-10)) (.leaf (-5))))),
  (.branch 64 (.branch 62 (.leaf (-35)) (.branch 63 (.leaf (-30)) (.leaf (-25)))) (.branch 66 (.branch 65 (.leaf (-20)) (.leaf (-15))) (.branch 67 (.leaf (-10)) (.leaf (-5))))),
  (.branch 28 (.leaf (-1)) (.leaf (0)))]
def witnessP9_288_4858 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (8)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (5)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (8))) (.branch 24 (.leaf (4)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (5))) (.branch 28 (.leaf (3)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (7)) (.leaf (0))) (.branch 32 (.leaf (6)) (.branch 33 (.leaf (1)) (.leaf (4)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (3)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (8)) (.leaf (4))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (2)) (.leaf (0))) (.branch 45 (.leaf (3)) (.leaf (7)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (6)) (.branch 50 (.leaf (5)) (.leaf (2))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (4)) (.leaf (0))) (.branch 54 (.leaf (3)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (8))) (.branch 58 (.leaf (4)) (.leaf (2))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (0)) (.leaf (5))) (.branch 62 (.leaf (3)) (.leaf (1)))) (.branch 65 (.branch 64 (.leaf (7)) (.leaf (0))) (.branch 66 (.leaf (6)) (.branch 67 (.leaf (2)) (.leaf (4)))))))))
  code := certificateP9_4858
  counts := ![(.branch 31 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 48 (.branch 40 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 53 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 33 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 63 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 59 (.leaf (7)) (.branch 67 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 26 (.branch 1 (.leaf (0)) (.branch 22 (.leaf (-10)) (.leaf (-12)))) (.branch 56 (.leaf (-13)) (.branch 60 (.leaf (-14)) (.leaf (-15))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 39 (.leaf (-19)) (.leaf (-21)))),
  (.branch 5 (.leaf (0)) (.branch 43 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (-1))) (.branch 58 (.leaf (-3)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-22))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (-10)) (.leaf (-11))))]
  high := ![(.branch 66 (.branch 61 (.leaf (-15)) (.leaf (-13))) (.branch 67 (.leaf (-10)) (.leaf (-7)))),
  (.branch 64 (.branch 48 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 56 (.leaf (-19)) (.leaf (-18)))) (.branch 66 (.branch 65 (.leaf (-15)) (.leaf (-12))) (.branch 67 (.leaf (-9)) (.leaf (-6))))),
  (.branch 52 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))),
  (.branch 65 (.branch 63 (.leaf (-12)) (.branch 64 (.leaf (-10)) (.leaf (-8)))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 61 (.branch 59 (.leaf (-5)) (.branch 60 (.leaf (-4)) (.leaf (-3)))) (.branch 62 (.leaf (-2)) (.branch 63 (.leaf (-1)) (.leaf (0))))),
  (.branch 64 (.branch 62 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 67 (.leaf (-2)) (.leaf (-1))),
  (.branch 65 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))),
  (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_288_4859 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (7))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (4)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (8)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (5))) (.branch 28 (.leaf (0)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (7)) (.branch 33 (.leaf (4)) (.leaf (2)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (6)) (.leaf (0))) (.branch 41 (.leaf (4)) (.leaf (1))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (2)) (.leaf (8))) (.branch 45 (.leaf (0)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (5)) (.branch 50 (.leaf (4)) (.leaf (2))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (3)) (.leaf (7)))) (.branch 57 (.branch 56 (.leaf (6)) (.leaf (0))) (.branch 58 (.leaf (4)) (.leaf (1))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (2)) (.leaf (5))) (.branch 62 (.leaf (0)) (.leaf (3)))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (0))) (.branch 66 (.leaf (8)) (.branch 67 (.leaf (4)) (.leaf (2)))))))))
  code := certificateP9_4859
  counts := ![(.branch 31 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 48 (.branch 40 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 45 (.leaf (10)) (.leaf (11)))) (.branch 57 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 62 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 67 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 31 (.branch 14 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 18 (.leaf (-8)) (.leaf (-9)))) (.branch 48 (.branch 35 (.leaf (-10)) (.leaf (-11))) (.branch 52 (.leaf (-12)) (.branch 65 (.leaf (-13)) (.leaf (-14)))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-22)) (.leaf (-23)))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 10 (.leaf (0)) (.branch 32 (.leaf (-38)) (.leaf (-40)))),
  (.branch 21 (.leaf (0)) (.branch 66 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 66 (.leaf (-14)) (.branch 67 (.leaf (-12)) (.leaf (-10)))),
  (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 65 (.branch 55 (.leaf (-11)) (.branch 64 (.leaf (-10)) (.leaf (-8)))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 59 (.leaf (-3)) (.leaf (-2))),
  (.branch 64 (.branch 62 (.branch 50 (.leaf (-23)) (.leaf (-21))) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 62 (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-11)) (.leaf (-10)))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 61 (.branch 57 (.branch 33 (.leaf (-40)) (.branch 56 (.leaf (-39)) (.leaf (-36)))) (.branch 59 (.branch 58 (.leaf (-33)) (.leaf (-30))) (.branch 60 (.leaf (-27)) (.leaf (-24))))) (.branch 64 (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 67 (.leaf (-6)) (.leaf (-3)))]
def witnessP9_288_4860 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (1))) (.branch 11 (.leaf (8)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (7)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (6)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (8))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (5)) (.leaf (4))) (.branch 28 (.leaf (7)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (6))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (1)) (.leaf (8)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (4)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (7)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (3))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (6)) (.leaf (2))) (.branch 45 (.leaf (8)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (5)) (.branch 50 (.leaf (7)) (.leaf (3))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (2)) (.leaf (0))) (.branch 54 (.leaf (6)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (4)) (.leaf (8))) (.branch 58 (.leaf (0)) (.leaf (2))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (5)) (.leaf (3))) (.branch 62 (.leaf (7)) (.leaf (1)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (6))) (.branch 66 (.leaf (4)) (.branch 67 (.leaf (2)) (.leaf (8)))))))))
  code := certificateP9_4860
  counts := ![(.branch 30 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 63 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 44 (.leaf (5)) (.leaf (6))) (.branch 59 (.leaf (7)) (.branch 67 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.leaf (7))))),
  (.branch 37 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 66 (.leaf (6)) (.leaf (7))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.leaf (-50))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (-14))) (.branch 36 (.leaf (-15)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-47)) (.leaf (-52)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (-12))) (.branch 46 (.leaf (-17)) (.leaf (-18)))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-22))) (.branch 26 (.leaf (-23)) (.leaf (-24)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (-7))) (.branch 31 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-19)) (.leaf (-20)))),
  (.branch 11 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 65 (.branch 36 (.leaf (-14)) (.branch 59 (.leaf (-13)) (.leaf (-12)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 64 (.branch 3 (.leaf (-50)) (.branch 56 (.leaf (-49)) (.leaf (-45)))) (.branch 66 (.branch 65 (.leaf (-36)) (.leaf (-27))) (.branch 67 (.leaf (-18)) (.leaf (-9))))),
  (.branch 37 (.leaf (-16)) (.branch 60 (.leaf (-13)) (.leaf (-9)))),
  (.branch 63 (.branch 52 (.branch 13 (.leaf (-52)) (.leaf (-51))) (.branch 62 (.leaf (-49)) (.leaf (-42)))) (.branch 65 (.branch 64 (.leaf (-35)) (.leaf (-28))) (.branch 66 (.leaf (-21)) (.branch 67 (.leaf (-14)) (.leaf (-7)))))),
  (.branch 57 (.branch 47 (.leaf (-18)) (.leaf (-16))) (.branch 67 (.leaf (-14)) (.leaf (-7)))),
  (.branch 64 (.branch 62 (.branch 61 (.leaf (-24)) (.leaf (-21))) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3)))),
  (.branch 64 (.branch 51 (.leaf (-20)) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 46 (.leaf (-1)) (.leaf (0)))]
def witnessP9_288_4861 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (7)) (.branch 16 (.leaf (0)) (.leaf (5))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (3))) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (6))) (.branch 24 (.leaf (1)) (.leaf (8))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (3)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (7)) (.leaf (2)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (6)))) (.branch 40 (.branch 39 (.leaf (8)) (.leaf (0))) (.branch 41 (.leaf (2)) (.leaf (1))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (5)) (.leaf (4))) (.branch 45 (.leaf (0)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (2))) (.branch 49 (.leaf (7)) (.branch 50 (.leaf (0)) (.leaf (6))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (1)) (.leaf (3))) (.branch 54 (.leaf (2)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (1)) (.leaf (8))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (0)) (.leaf (2))) (.branch 62 (.leaf (3)) (.leaf (6)))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (0))) (.branch 66 (.leaf (4)) (.branch 67 (.leaf (7)) (.leaf (2)))))))))
  code := certificateP9_4861
  counts := ![(.branch 31 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 50 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 60 (.branch 55 (.leaf (11)) (.leaf (12))) (.branch 65 (.leaf (13)) (.leaf (14)))))),
  (.branch 30 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 41 (.leaf (5)) (.branch 48 (.leaf (6)) (.leaf (7)))) (.branch 61 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 67 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-27))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-15))) (.branch 18 (.leaf (-17)) (.branch 52 (.leaf (-20)) (.leaf (-22))))),
  (.branch 20 (.leaf (0)) (.leaf (-2))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 53 (.leaf (-21)) (.leaf (-23)))),
  (.branch 32 (.branch 10 (.leaf (0)) (.leaf (-3))) (.branch 66 (.leaf (-5)) (.leaf (-6)))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 29 (.leaf (-11)) (.leaf (-13)))),
  (.branch 9 (.leaf (0)) (.branch 63 (.leaf (-5)) (.leaf (-7)))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 39 (.leaf (-14)) (.leaf (-18))))]
  high := ![(.branch 51 (.branch 41 (.branch 36 (.leaf (-27)) (.leaf (-26))) (.branch 46 (.leaf (-25)) (.leaf (-24)))) (.branch 61 (.branch 56 (.leaf (-23)) (.leaf (-22))) (.branch 66 (.leaf (-21)) (.branch 67 (.leaf (-14)) (.leaf (-7)))))),
  (.branch 65 (.branch 53 (.leaf (-22)) (.branch 59 (.leaf (-21)) (.leaf (-20)))) (.branch 66 (.leaf (-16)) (.branch 67 (.leaf (-12)) (.leaf (-8))))),
  (.branch 55 (.leaf (-2)) (.branch 62 (.leaf (-1)) (.leaf (0)))),
  (.branch 64 (.branch 54 (.leaf (-23)) (.branch 63 (.leaf (-22)) (.leaf (-19)))) (.branch 66 (.branch 65 (.leaf (-16)) (.leaf (-13))) (.branch 67 (.leaf (-10)) (.leaf (-7))))),
  (.branch 67 (.leaf (-6)) (.leaf (-4))),
  (.branch 62 (.branch 59 (.branch 58 (.leaf (-13)) (.leaf (-12))) (.branch 60 (.leaf (-11)) (.branch 61 (.leaf (-10)) (.leaf (-9))))) (.branch 65 (.branch 63 (.leaf (-8)) (.branch 64 (.leaf (-7)) (.leaf (-6)))) (.branch 66 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 65 (.branch 64 (.leaf (-7)) (.leaf (-6))) (.branch 66 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3))))),
  (.branch 50 (.leaf (-2)) (.leaf (-1))),
  (.branch 63 (.branch 60 (.branch 40 (.leaf (-18)) (.leaf (-17))) (.branch 61 (.leaf (-16)) (.branch 62 (.leaf (-15)) (.leaf (-14))))) (.branch 65 (.branch 64 (.leaf (-13)) (.leaf (-12))) (.branch 66 (.leaf (-11)) (.branch 67 (.leaf (-10)) (.leaf (-9))))))]
def witnessP9_288_4862 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (7)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (1)) (.leaf (8))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (3)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (5)) (.leaf (4))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (7)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (2)) (.leaf (5)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (6)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (8)) (.leaf (4))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (1)) (.leaf (0))) (.branch 45 (.leaf (3)) (.leaf (5)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (4)) (.branch 50 (.leaf (1)) (.leaf (7))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (2))) (.branch 54 (.leaf (3)) (.leaf (6)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (5)) (.leaf (4))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (2)) (.leaf (0))) (.branch 62 (.leaf (3)) (.leaf (8)))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (0))) (.branch 66 (.leaf (4)) (.branch 67 (.leaf (2)) (.leaf (5)))))))))
  code := certificateP9_4862
  counts := ![(.branch 31 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 48 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 61 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 36 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 40 (.leaf (5)) (.branch 47 (.leaf (6)) (.leaf (7)))) (.branch 60 (.leaf (8)) (.branch 67 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 58 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-24))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 32 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (-1)) (.leaf (-3)))) (.branch 49 (.leaf (-4)) (.branch 66 (.leaf (-5)) (.leaf (-6))))),
  (.branch 34 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (-16))) (.branch 51 (.leaf (-17)) (.leaf (-18)))),
  (.branch 17 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 66 (.branch 57 (.leaf (-14)) (.leaf (-12))) (.branch 67 (.leaf (-8)) (.leaf (-4)))),
  (.branch 58 (.branch 44 (.branch 37 (.leaf (-24)) (.leaf (-23))) (.branch 51 (.leaf (-22)) (.leaf (-21)))) (.branch 66 (.branch 65 (.leaf (-20)) (.leaf (-15))) (.branch 67 (.leaf (-10)) (.leaf (-5))))),
  (.branch 54 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))),
  (.branch 65 (.branch 63 (.leaf (-12)) (.branch 64 (.leaf (-10)) (.leaf (-8)))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 67 (.leaf (-6)) (.leaf (-5))),
  (.branch 35 (.leaf (-1)) (.leaf (0))),
  (.branch 61 (.branch 58 (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))) (.branch 59 (.leaf (-10)) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (-18)) (.leaf (-17))) (.branch 54 (.leaf (-16)) (.leaf (-15)))) (.branch 57 (.branch 56 (.leaf (-14)) (.leaf (-13))) (.branch 58 (.leaf (-12)) (.leaf (-11))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (-10)) (.leaf (-9))) (.branch 62 (.leaf (-8)) (.leaf (-7)))) (.branch 65 (.branch 64 (.leaf (-6)) (.leaf (-5))) (.branch 66 (.leaf (-4)) (.branch 67 (.leaf (-3)) (.leaf (-2))))))),
  (.branch 65 (.branch 64 (.leaf (-6)) (.leaf (-5))) (.branch 66 (.leaf (-4)) (.branch 67 (.leaf (-3)) (.leaf (-2)))))]
def witnessP9_288_4863 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (6)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (5)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (6))) (.branch 28 (.leaf (3)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (8)) (.leaf (0))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (1)) (.leaf (5)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (3)) (.leaf (6)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (2)) (.leaf (0))) (.branch 45 (.leaf (3)) (.leaf (7)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (4)) (.branch 50 (.leaf (6)) (.leaf (2))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (5)) (.leaf (0))) (.branch 54 (.leaf (3)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (2))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (0)) (.leaf (6))) (.branch 62 (.leaf (3)) (.leaf (1)))) (.branch 65 (.branch 64 (.leaf (8)) (.leaf (0))) (.branch 66 (.leaf (4)) (.branch 67 (.leaf (2)) (.leaf (5)))))))))
  code := certificateP9_4863
  counts := ![(.branch 31 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 48 (.branch 40 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 53 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 33 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 63 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 59 (.leaf (7)) (.branch 67 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.branch 64 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 26 (.branch 1 (.leaf (0)) (.branch 22 (.leaf (-10)) (.leaf (-12)))) (.branch 56 (.leaf (-13)) (.branch 60 (.leaf (-14)) (.leaf (-15))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 39 (.leaf (-19)) (.leaf (-21)))),
  (.branch 5 (.leaf (0)) (.branch 43 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (-3))) (.branch 23 (.leaf (-4)) (.leaf (-5)))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (-1))) (.branch 58 (.leaf (-3)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-22))),
  (.branch 12 (.leaf (0)) (.leaf (-22))),
  (.branch 30 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 66 (.branch 61 (.leaf (-15)) (.leaf (-13))) (.branch 67 (.leaf (-10)) (.leaf (-7)))),
  (.branch 64 (.branch 48 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 56 (.leaf (-19)) (.leaf (-18)))) (.branch 66 (.branch 65 (.leaf (-15)) (.leaf (-12))) (.branch 67 (.leaf (-9)) (.leaf (-6))))),
  (.branch 52 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))),
  (.branch 65 (.branch 63 (.leaf (-12)) (.branch 64 (.leaf (-10)) (.leaf (-8)))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 58 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-2)))),
  (.branch 61 (.branch 59 (.leaf (-5)) (.branch 60 (.leaf (-4)) (.leaf (-3)))) (.branch 62 (.leaf (-2)) (.branch 63 (.leaf (-1)) (.leaf (0))))),
  (.branch 64 (.branch 62 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.branch 51 (.branch 48 (.branch 47 (.leaf (-22)) (.leaf (-21))) (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-19)) (.leaf (-18))))) (.branch 54 (.branch 52 (.leaf (-17)) (.branch 53 (.leaf (-16)) (.leaf (-15)))) (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))))) (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_288_4864 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (2)) (.leaf (5))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (8)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (7)) (.branch 33 (.leaf (2)) (.leaf (4)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (6)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (5)) (.leaf (1))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (8)) (.leaf (0))) (.branch 45 (.leaf (2)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (3)) (.branch 50 (.leaf (2)) (.leaf (5))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (7)) (.leaf (6)))) (.branch 57 (.branch 56 (.leaf (2)) (.leaf (0))) (.branch 58 (.leaf (4)) (.leaf (1))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (3)) (.leaf (0))) (.branch 62 (.leaf (2)) (.leaf (5)))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (0))) (.branch 66 (.leaf (8)) (.branch 67 (.leaf (2)) (.leaf (4)))))))))
  code := certificateP9_4864
  counts := ![(.branch 31 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 48 (.branch 40 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 57 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 61 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 67 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 58 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 43 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-25))),
  (.branch 34 (.leaf (0)) (.leaf (-1))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (-9))) (.branch 51 (.leaf (-12)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 9 (.leaf (0)) (.branch 54 (.leaf (-41)) (.leaf (-42)))),
  (.branch 20 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 66 (.branch 53 (.leaf (-13)) (.leaf (-12))) (.branch 67 (.leaf (-8)) (.leaf (-4)))),
  (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 63 (.branch 61 (.branch 38 (.leaf (-25)) (.leaf (-24))) (.branch 62 (.leaf (-21)) (.leaf (-18)))) (.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-12))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 35 (.leaf (-1)) (.leaf (0))),
  (.branch 65 (.branch 52 (.leaf (-13)) (.branch 64 (.leaf (-12)) (.leaf (-10)))) (.branch 66 (.leaf (-8)) (.branch 67 (.leaf (-6)) (.leaf (-4))))),
  (.branch 61 (.branch 58 (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))) (.branch 59 (.leaf (-10)) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 61 (.branch 57 (.branch 55 (.leaf (-42)) (.branch 56 (.leaf (-39)) (.leaf (-36)))) (.branch 59 (.branch 58 (.leaf (-33)) (.leaf (-30))) (.branch 60 (.leaf (-27)) (.leaf (-24))))) (.branch 64 (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 44 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 67 (.leaf (-6)) (.leaf (-3))))]
def witnessP9_288_4865 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (5))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (8)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (6)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (4)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (7)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (5)) (.leaf (1))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (2)) (.leaf (3))) (.branch 45 (.leaf (0)) (.leaf (6)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (4))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (2)) (.leaf (3))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (8)) (.leaf (5)))) (.branch 57 (.branch 56 (.leaf (2)) (.leaf (0))) (.branch 58 (.leaf (3)) (.leaf (1))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (2)) (.leaf (0))) (.branch 62 (.leaf (4)) (.leaf (6)))) (.branch 65 (.branch 64 (.leaf (3)) (.leaf (1))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (2)) (.leaf (5)))))))))
  code := certificateP9_4865
  counts := ![(.branch 32 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 49 (.branch 40 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 45 (.leaf (10)) (.leaf (11)))) (.branch 57 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 61 (.leaf (14)) (.branch 66 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 16 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 39 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 67 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 34 (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 62 (.leaf (4)) (.leaf (5))))),
  (.branch 41 (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 55 (.leaf (3)) (.branch 68 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 35 (.leaf (-9)) (.branch 52 (.leaf (-11)) (.leaf (-13))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (-1)) (.leaf (-3)))) (.branch 43 (.leaf (-4)) (.branch 60 (.leaf (-5)) (.leaf (-6))))),
  (.branch 3 (.leaf (0)) (.branch 30 (.leaf (-19)) (.leaf (-20)))),
  (.branch 7 (.leaf (0)) (.branch 34 (.leaf (-33)) (.leaf (-34)))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-30))),
  (.branch 20 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 62 (.leaf (-13)) (.branch 67 (.leaf (-12)) (.leaf (-10)))),
  (.branch 60 (.branch 48 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.leaf (-6)) (.leaf (-5))),
  (.branch 66 (.branch 65 (.leaf (-20)) (.leaf (-15))) (.branch 67 (.leaf (-10)) (.leaf (-5)))),
  (.branch 64 (.branch 49 (.branch 35 (.leaf (-34)) (.leaf (-32))) (.branch 63 (.leaf (-30)) (.leaf (-25)))) (.branch 66 (.branch 65 (.leaf (-20)) (.leaf (-15))) (.branch 67 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 45 (.branch 41 (.branch 39 (.leaf (-30)) (.branch 40 (.leaf (-29)) (.leaf (-28)))) (.branch 43 (.branch 42 (.leaf (-27)) (.leaf (-26))) (.branch 44 (.leaf (-25)) (.leaf (-24))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (-23)) (.leaf (-22))) (.branch 48 (.leaf (-21)) (.leaf (-20)))) (.branch 51 (.branch 50 (.leaf (-19)) (.leaf (-18))) (.branch 52 (.leaf (-17)) (.leaf (-16)))))) (.branch 60 (.branch 56 (.branch 54 (.leaf (-15)) (.branch 55 (.leaf (-14)) (.leaf (-13)))) (.branch 58 (.branch 57 (.leaf (-12)) (.leaf (-11))) (.branch 59 (.leaf (-10)) (.leaf (-9))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 61 (.branch 57 (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_288_4866 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (7))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (0)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (8)) (.leaf (0))) (.branch 24 (.leaf (1)) (.leaf (5))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (0)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (6)) (.branch 33 (.leaf (0)) (.leaf (7)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (4)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (1)) (.leaf (5))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (8))) (.branch 45 (.leaf (0)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (6)) (.branch 50 (.leaf (0)) (.leaf (2))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (4)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (7)) (.leaf (0))) (.branch 58 (.leaf (1)) (.leaf (5))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (0)) (.leaf (2))) (.branch 62 (.leaf (0)) (.leaf (3)))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (0))) (.branch 66 (.leaf (6)) (.branch 67 (.leaf (0)) (.leaf (8)))))))))
  code := certificateP9_4866
  counts := ![(.branch 33 (.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 18 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))) (.branch 28 (.branch 26 (.leaf (10)) (.leaf (11))) (.branch 31 (.leaf (12)) (.leaf (13)))))) (.branch 50 (.branch 40 (.branch 35 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16)))) (.branch 45 (.branch 43 (.leaf (17)) (.leaf (18))) (.branch 48 (.leaf (19)) (.leaf (20))))) (.branch 60 (.branch 55 (.branch 52 (.leaf (21)) (.leaf (22))) (.branch 57 (.leaf (23)) (.leaf (24)))) (.branch 65 (.branch 62 (.leaf (25)) (.leaf (26))) (.branch 67 (.leaf (27)) (.leaf (28))))))),
  (.branch 30 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4))))),
  (.branch 34 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 68 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-10))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.branch 27 (.branch 5 (.leaf (0)) (.leaf (-13))) (.branch 61 (.leaf (-15)) (.leaf (-16)))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-13))),
  (.branch 22 (.leaf (0)) (.branch 44 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 58 (.branch 53 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-8)) (.leaf (-7)))),
  (.branch 65 (.branch 59 (.leaf (-13)) (.leaf (-12))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 64 (.branch 62 (.leaf (-16)) (.branch 63 (.leaf (-14)) (.leaf (-12)))) (.branch 66 (.branch 65 (.leaf (-10)) (.leaf (-8))) (.branch 67 (.leaf (-6)) (.leaf (-4))))),
  (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))),
  (.branch 61 (.branch 57 (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 67 (.leaf (-2)) (.leaf (-1))),
  (.branch 62 (.branch 59 (.branch 57 (.leaf (-13)) (.branch 58 (.leaf (-12)) (.leaf (-11)))) (.branch 60 (.leaf (-10)) (.branch 61 (.leaf (-9)) (.leaf (-8))))) (.branch 65 (.branch 63 (.leaf (-7)) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.leaf (-4)) (.branch 67 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 45 (.leaf (-2)) (.branch 46 (.leaf (-1)) (.leaf (0))))]
def witnessP9_288_4867 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (7))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (0)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (3)) (.leaf (2)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (4)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (6))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (2)) (.leaf (1))) (.branch 45 (.leaf (0)) (.leaf (5)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (1))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (3)) (.leaf (2))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (4)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (2)) (.leaf (1))) (.branch 58 (.leaf (0)) (.leaf (8))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (2)) (.leaf (1))) (.branch 62 (.leaf (0)) (.leaf (5)))) (.branch 65 (.branch 64 (.leaf (2)) (.leaf (1))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (3)) (.leaf (2)))))))))
  code := certificateP9_4867
  counts := ![(.branch 32 (.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))))) (.branch 49 (.branch 38 (.branch 35 (.leaf (10)) (.leaf (11))) (.branch 41 (.leaf (12)) (.branch 45 (.leaf (13)) (.leaf (14))))) (.branch 58 (.branch 52 (.leaf (15)) (.branch 55 (.leaf (16)) (.leaf (17)))) (.branch 62 (.leaf (18)) (.branch 66 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 48 (.branch 40 (.branch 36 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 57 (.branch 53 (.leaf (12)) (.leaf (13))) (.branch 61 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 34 (.branch 17 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))) (.branch 51 (.branch 43 (.branch 39 (.leaf (8)) (.leaf (9))) (.branch 47 (.leaf (10)) (.leaf (11)))) (.branch 60 (.branch 56 (.leaf (12)) (.leaf (13))) (.branch 64 (.leaf (14)) (.branch 68 (.leaf (15)) (.leaf (16))))))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 67 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 59 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))) (.branch 41 (.branch 24 (.leaf (-7)) (.leaf (-8))) (.branch 58 (.leaf (-9)) (.leaf (-10))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.leaf (0)),
  (.branch 16 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-26))),
  (.branch 25 (.leaf (0)) (.leaf (-43))),
  (.branch 59 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 63 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 67 (.leaf (-8)) (.leaf (-6)))),
  (.branch 66 (.leaf (-12)) (.branch 67 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 61 (.branch 57 (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 48 (.branch 45 (.branch 43 (.leaf (-26)) (.branch 44 (.leaf (-25)) (.leaf (-24)))) (.branch 46 (.leaf (-23)) (.branch 47 (.leaf (-22)) (.leaf (-21))))) (.branch 51 (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-19)) (.leaf (-18)))) (.branch 53 (.branch 52 (.leaf (-17)) (.leaf (-16))) (.branch 54 (.leaf (-15)) (.leaf (-14)))))) (.branch 61 (.branch 58 (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))) (.branch 59 (.leaf (-10)) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 35 (.branch 30 (.branch 27 (.branch 26 (.leaf (-43)) (.leaf (-42))) (.branch 28 (.leaf (-41)) (.branch 29 (.leaf (-40)) (.leaf (-39))))) (.branch 32 (.branch 31 (.leaf (-38)) (.leaf (-37))) (.branch 33 (.leaf (-36)) (.branch 34 (.leaf (-35)) (.leaf (-34)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-33)) (.leaf (-32))) (.branch 38 (.leaf (-31)) (.branch 39 (.leaf (-30)) (.leaf (-29))))) (.branch 43 (.branch 41 (.leaf (-28)) (.branch 42 (.leaf (-27)) (.leaf (-26)))) (.branch 44 (.leaf (-25)) (.branch 45 (.leaf (-24)) (.leaf (-23))))))) (.branch 57 (.branch 51 (.branch 48 (.branch 47 (.leaf (-22)) (.leaf (-21))) (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-19)) (.leaf (-18))))) (.branch 54 (.branch 52 (.leaf (-17)) (.branch 53 (.leaf (-16)) (.leaf (-15)))) (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))))) (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_288_4868 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (7)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (8))) (.branch 24 (.leaf (1)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (0)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (0))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (6)) (.leaf (2)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (4)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (3)) (.leaf (7))) (.branch 41 (.leaf (1)) (.leaf (0))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (2)) (.leaf (1))) (.branch 45 (.leaf (0)) (.leaf (8)))) (.branch 48 (.branch 47 (.leaf (3)) (.leaf (0))) (.branch 49 (.leaf (1)) (.branch 50 (.leaf (5)) (.leaf (2))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (4)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (3)) (.leaf (6))) (.branch 58 (.leaf (1)) (.leaf (0))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (2)) (.leaf (1))) (.branch 62 (.leaf (0)) (.leaf (7)))) (.branch 65 (.branch 64 (.leaf (3)) (.leaf (0))) (.branch 66 (.leaf (1)) (.branch 67 (.leaf (8)) (.leaf (2)))))))))
  code := certificateP9_4868
  counts := ![(.branch 31 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))))) (.branch 48 (.branch 38 (.branch 35 (.leaf (10)) (.leaf (11))) (.branch 42 (.leaf (12)) (.branch 45 (.leaf (13)) (.leaf (14))))) (.branch 59 (.branch 52 (.leaf (15)) (.branch 55 (.leaf (16)) (.leaf (17)))) (.branch 62 (.leaf (18)) (.branch 65 (.leaf (19)) (.leaf (20))))))),
  (.branch 32 (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 49 (.branch 41 (.branch 36 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 58 (.branch 53 (.leaf (12)) (.leaf (13))) (.branch 61 (.leaf (14)) (.branch 66 (.leaf (15)) (.leaf (16))))))),
  (.branch 34 (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3)))),
  (.branch 46 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 67 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 27 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-7)) (.leaf (-9)))) (.branch 44 (.leaf (-10)) (.branch 61 (.leaf (-11)) (.leaf (-12))))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 6 (.leaf (0)) (.branch 50 (.leaf (-17)) (.leaf (-19)))),
  (.branch 12 (.leaf (0)) (.branch 33 (.leaf (-11)) (.leaf (-13)))),
  (.branch 16 (.leaf (0)) (.leaf (-7))),
  (.branch 67 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 66 (.leaf (-15)) (.branch 67 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.leaf (-12)) (.branch 67 (.leaf (-10)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-6))) (.branch 67 (.leaf (-4)) (.leaf (-2)))),
  (.branch 61 (.branch 57 (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.branch 54 (.branch 52 (.branch 51 (.leaf (-19)) (.leaf (-18))) (.branch 53 (.leaf (-17)) (.leaf (-16)))) (.branch 56 (.branch 55 (.leaf (-15)) (.leaf (-14))) (.branch 57 (.leaf (-13)) (.branch 58 (.leaf (-12)) (.leaf (-11)))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (-10)) (.leaf (-9))) (.branch 62 (.leaf (-8)) (.leaf (-7)))) (.branch 65 (.branch 64 (.leaf (-6)) (.leaf (-5))) (.branch 66 (.leaf (-4)) (.branch 67 (.leaf (-3)) (.leaf (-2))))))),
  (.branch 62 (.branch 59 (.branch 34 (.leaf (-13)) (.branch 58 (.leaf (-12)) (.leaf (-11)))) (.branch 60 (.leaf (-10)) (.branch 61 (.leaf (-9)) (.leaf (-8))))) (.branch 65 (.branch 63 (.leaf (-7)) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.leaf (-4)) (.branch 67 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 65 (.branch 17 (.leaf (-7)) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.leaf (-4)) (.branch 67 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-2))]
def witnessP9_288_4869 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (6)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (5))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (5)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (7)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (5)) (.leaf (3)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (4)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (6)) (.leaf (0))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (3)) (.leaf (5))) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (1))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (4)) (.leaf (3))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (5)) (.leaf (2)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (8)) (.leaf (0))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (1)) (.leaf (0)))) (.branch 65 (.branch 64 (.leaf (2)) (.leaf (1))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (5)) (.leaf (3)))))))))
  code := certificateP9_4869
  counts := ![(.branch 32 (.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))) (.branch 49 (.branch 39 (.branch 35 (.leaf (10)) (.leaf (11))) (.branch 42 (.leaf (12)) (.branch 46 (.leaf (13)) (.leaf (14))))) (.branch 59 (.branch 52 (.leaf (15)) (.branch 56 (.leaf (16)) (.leaf (17)))) (.branch 63 (.leaf (18)) (.branch 66 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 48 (.branch 40 (.branch 36 (.leaf (8)) (.leaf (9))) (.branch 45 (.leaf (10)) (.leaf (11)))) (.branch 57 (.branch 53 (.leaf (12)) (.leaf (13))) (.branch 62 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 67 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 58 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-12))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))) (.branch 48 (.branch 31 (.leaf (-10)) (.leaf (-11))) (.branch 65 (.leaf (-12)) (.leaf (-13))))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 37 (.leaf (-9)) (.leaf (-11)))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (-2))) (.branch 54 (.leaf (-4)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-27))),
  (.branch 24 (.leaf (0)) (.leaf (-44))),
  (.branch 58 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 60 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 67 (.leaf (-10)) (.leaf (-5)))),
  (.branch 66 (.leaf (-13)) (.branch 67 (.leaf (-10)) (.leaf (-7)))),
  (.branch 65 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 64 (.branch 62 (.leaf (-11)) (.branch 63 (.leaf (-10)) (.leaf (-9)))) (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-7))) (.branch 67 (.leaf (-6)) (.leaf (-5))))),
  (.branch 55 (.leaf (-6)) (.leaf (-5))),
  (.branch 54 (.branch 47 (.branch 44 (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-26)) (.leaf (-25)))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-23)) (.leaf (-22))))) (.branch 50 (.branch 48 (.leaf (-21)) (.branch 49 (.leaf (-20)) (.leaf (-19)))) (.branch 52 (.branch 51 (.leaf (-18)) (.leaf (-17))) (.branch 53 (.leaf (-16)) (.leaf (-15)))))) (.branch 61 (.branch 57 (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 35 (.branch 29 (.branch 26 (.branch 25 (.leaf (-44)) (.leaf (-43))) (.branch 27 (.leaf (-42)) (.branch 28 (.leaf (-41)) (.leaf (-40))))) (.branch 32 (.branch 30 (.leaf (-39)) (.branch 31 (.leaf (-38)) (.leaf (-37)))) (.branch 33 (.leaf (-36)) (.branch 34 (.leaf (-35)) (.leaf (-34)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-33)) (.leaf (-32))) (.branch 38 (.leaf (-31)) (.branch 39 (.leaf (-30)) (.leaf (-29))))) (.branch 43 (.branch 41 (.leaf (-28)) (.branch 42 (.leaf (-27)) (.leaf (-26)))) (.branch 44 (.leaf (-25)) (.branch 45 (.leaf (-24)) (.leaf (-23))))))) (.branch 57 (.branch 51 (.branch 48 (.branch 47 (.leaf (-22)) (.leaf (-21))) (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-19)) (.leaf (-18))))) (.branch 54 (.branch 52 (.leaf (-17)) (.branch 53 (.leaf (-16)) (.leaf (-15)))) (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))))) (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_288_4870 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (7))) (.branch 7 (.leaf (3)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (5)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (6))) (.branch 24 (.leaf (2)) (.leaf (5))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (4)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (5)) (.leaf (3)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (4)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (8))) (.branch 41 (.leaf (3)) (.leaf (5))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (1)) (.leaf (0))) (.branch 45 (.leaf (2)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (3))) (.branch 49 (.leaf (1)) (.branch 50 (.leaf (5)) (.leaf (2))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (4)) (.leaf (3)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (6))) (.branch 58 (.leaf (2)) (.leaf (5))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (1)) (.leaf (0))) (.branch 62 (.leaf (3)) (.leaf (4)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (2))) (.branch 66 (.leaf (1)) (.branch 67 (.leaf (5)) (.leaf (3)))))))))
  code := certificateP9_4870
  counts := ![(.branch 30 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 61 (.leaf (14)) (.branch 64 (.leaf (15)) (.leaf (16))))))),
  (.branch 32 (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 36 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 38 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 65 (.leaf (9)) (.leaf (10)))))),
  (.branch 34 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 55 (.branch 41 (.leaf (5)) (.branch 48 (.leaf (6)) (.leaf (7)))) (.branch 62 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 67 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.leaf (0)) (.branch 57 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))) (.branch 47 (.branch 30 (.leaf (-13)) (.leaf (-14))) (.branch 64 (.leaf (-15)) (.leaf (-16))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 36 (.leaf (-5)) (.branch 53 (.leaf (-6)) (.leaf (-7))))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-14)) (.leaf (-17)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 23 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.leaf (-62))),
  (.branch 40 (.leaf (0)) (.leaf (-28)))]
  high := ![(.branch 66 (.branch 65 (.leaf (-16)) (.leaf (-13))) (.branch 67 (.leaf (-10)) (.leaf (-7)))),
  (.branch 54 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5)))),
  (.branch 59 (.branch 52 (.leaf (-17)) (.leaf (-16))) (.branch 66 (.leaf (-15)) (.branch 67 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 65 (.branch 55 (.leaf (-11)) (.branch 64 (.leaf (-10)) (.leaf (-8)))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 21 (.branch 13 (.branch 9 (.branch 7 (.leaf (-62)) (.branch 8 (.leaf (-61)) (.leaf (-60)))) (.branch 11 (.branch 10 (.leaf (-59)) (.leaf (-58))) (.branch 12 (.leaf (-57)) (.leaf (-56))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-55)) (.leaf (-54))) (.branch 16 (.leaf (-53)) (.leaf (-52)))) (.branch 19 (.branch 18 (.leaf (-51)) (.leaf (-50))) (.branch 20 (.leaf (-49)) (.leaf (-48)))))) (.branch 29 (.branch 25 (.branch 23 (.branch 22 (.leaf (-47)) (.leaf (-46))) (.branch 24 (.leaf (-45)) (.leaf (-44)))) (.branch 27 (.branch 26 (.leaf (-43)) (.leaf (-42))) (.branch 28 (.leaf (-41)) (.leaf (-40))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-39)) (.leaf (-38))) (.branch 32 (.leaf (-37)) (.leaf (-36)))) (.branch 35 (.branch 34 (.leaf (-35)) (.leaf (-34))) (.branch 36 (.leaf (-33)) (.leaf (-32))))))) (.branch 52 (.branch 44 (.branch 40 (.branch 38 (.leaf (-31)) (.branch 39 (.leaf (-30)) (.leaf (-29)))) (.branch 42 (.branch 41 (.leaf (-28)) (.leaf (-27))) (.branch 43 (.leaf (-26)) (.leaf (-25))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-24)) (.leaf (-23))) (.branch 47 (.leaf (-22)) (.leaf (-21)))) (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-19))) (.branch 51 (.leaf (-18)) (.leaf (-17)))))) (.branch 60 (.branch 56 (.branch 54 (.branch 53 (.leaf (-16)) (.leaf (-15))) (.branch 55 (.leaf (-14)) (.leaf (-13)))) (.branch 58 (.branch 57 (.leaf (-12)) (.leaf (-11))) (.branch 59 (.leaf (-10)) (.leaf (-9))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 54 (.branch 47 (.branch 43 (.branch 41 (.leaf (-28)) (.branch 42 (.leaf (-27)) (.leaf (-26)))) (.branch 45 (.branch 44 (.leaf (-25)) (.leaf (-24))) (.branch 46 (.leaf (-23)) (.leaf (-22))))) (.branch 50 (.branch 48 (.leaf (-21)) (.branch 49 (.leaf (-20)) (.leaf (-19)))) (.branch 52 (.branch 51 (.leaf (-18)) (.leaf (-17))) (.branch 53 (.leaf (-16)) (.leaf (-15)))))) (.branch 61 (.branch 57 (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_288_4871 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (4))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (4))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (5)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (1)) (.leaf (7))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (4))) (.branch 28 (.leaf (3)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (4))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (5)) (.leaf (3)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (4)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (3)) (.leaf (0))) (.branch 41 (.leaf (1)) (.leaf (6))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (2)) (.leaf (4))) (.branch 45 (.leaf (3)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (4))) (.branch 49 (.leaf (2)) (.branch 50 (.leaf (5)) (.leaf (3))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (4)) (.leaf (2)))) (.branch 57 (.branch 56 (.leaf (3)) (.leaf (0))) (.branch 58 (.leaf (1)) (.leaf (8))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (2)) (.leaf (4))) (.branch 62 (.leaf (3)) (.leaf (0)))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (4))) (.branch 66 (.leaf (2)) (.branch 67 (.leaf (5)) (.leaf (3)))))))))
  code := certificateP9_4871
  counts := ![(.branch 29 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 38 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 14 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 61 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 67 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 59 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-14)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-5)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 31 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))) (.branch 48 (.leaf (-5)) (.branch 65 (.leaf (-6)) (.leaf (-7))))),
  (.branch 16 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-26))),
  (.branch 25 (.leaf (0)) (.leaf (-43))),
  (.branch 59 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 65 (.branch 58 (.leaf (-16)) (.branch 64 (.leaf (-15)) (.leaf (-12)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 65 (.branch 59 (.leaf (-13)) (.leaf (-12))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-3)))),
  (.branch 57 (.leaf (-2)) (.branch 63 (.leaf (-1)) (.leaf (0)))),
  (.branch 66 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5)))),
  (.leaf (-1)),
  (.branch 55 (.branch 48 (.branch 45 (.branch 43 (.leaf (-26)) (.branch 44 (.leaf (-25)) (.leaf (-24)))) (.branch 46 (.leaf (-23)) (.branch 47 (.leaf (-22)) (.leaf (-21))))) (.branch 51 (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-19)) (.leaf (-18)))) (.branch 53 (.branch 52 (.leaf (-17)) (.leaf (-16))) (.branch 54 (.leaf (-15)) (.leaf (-14)))))) (.branch 61 (.branch 58 (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))) (.branch 59 (.leaf (-10)) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 35 (.branch 30 (.branch 27 (.branch 26 (.leaf (-43)) (.leaf (-42))) (.branch 28 (.leaf (-41)) (.branch 29 (.leaf (-40)) (.leaf (-39))))) (.branch 32 (.branch 31 (.leaf (-38)) (.leaf (-37))) (.branch 33 (.leaf (-36)) (.branch 34 (.leaf (-35)) (.leaf (-34)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-33)) (.leaf (-32))) (.branch 38 (.leaf (-31)) (.branch 39 (.leaf (-30)) (.leaf (-29))))) (.branch 43 (.branch 41 (.leaf (-28)) (.branch 42 (.leaf (-27)) (.leaf (-26)))) (.branch 44 (.leaf (-25)) (.branch 45 (.leaf (-24)) (.leaf (-23))))))) (.branch 57 (.branch 51 (.branch 48 (.branch 47 (.leaf (-22)) (.leaf (-21))) (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-19)) (.leaf (-18))))) (.branch 54 (.branch 52 (.leaf (-17)) (.branch 53 (.leaf (-16)) (.leaf (-15)))) (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))))) (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_288_4872 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (7)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (8))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (6))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (3)) (.leaf (0))) (.branch 20 (.leaf (7)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (4))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (6))) (.branch 28 (.leaf (3)) (.leaf (8)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (5)) (.leaf (7)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (4)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (6)) (.leaf (0))) (.branch 41 (.leaf (8)) (.leaf (2))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (1)) (.leaf (0))) (.branch 45 (.leaf (5)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (4)) (.leaf (7))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (6))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (2)) (.leaf (0))) (.branch 54 (.leaf (8)) (.leaf (5)))) (.branch 57 (.branch 56 (.leaf (3)) (.leaf (1))) (.branch 58 (.leaf (0)) (.leaf (4))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (0)) (.leaf (6))) (.branch 62 (.leaf (2)) (.leaf (7)))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (0))) (.branch 66 (.leaf (3)) (.branch 67 (.leaf (5)) (.leaf (8)))))))))
  code := certificateP9_4872
  counts := ![(.branch 31 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 49 (.branch 40 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 58 (.branch 53 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 36 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.leaf (7))))),
  (.branch 38 (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 66 (.leaf (6)) (.leaf (7))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 67 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 41 (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 54 (.leaf (3)) (.branch 68 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 26 (.branch 1 (.leaf (0)) (.leaf (-24))) (.branch 60 (.leaf (-35)) (.leaf (-45)))),
  (.branch 2 (.leaf (0)) (.leaf (-24))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-35)) (.leaf (-46)))),
  (.branch 8 (.leaf (0)) (.branch 46 (.leaf (-11)) (.leaf (-19)))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 47 (.leaf (-20)) (.leaf (-21)))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (-1))) (.branch 55 (.leaf (-4)) (.leaf (-5)))),
  (.branch 27 (.branch 5 (.leaf (0)) (.leaf (-13))) (.branch 61 (.leaf (-15)) (.leaf (-16)))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-8)))),
  (.branch 41 (.leaf (0)) (.branch 54 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 66 (.branch 61 (.leaf (-45)) (.leaf (-41))) (.branch 67 (.leaf (-34)) (.leaf (-27)))),
  (.branch 58 (.branch 44 (.branch 37 (.leaf (-24)) (.leaf (-23))) (.branch 51 (.leaf (-22)) (.leaf (-21)))) (.branch 66 (.branch 65 (.leaf (-20)) (.leaf (-15))) (.branch 67 (.leaf (-10)) (.leaf (-5))))),
  (.branch 53 (.branch 23 (.branch 13 (.leaf (-46)) (.leaf (-45))) (.branch 33 (.leaf (-44)) (.branch 43 (.leaf (-43)) (.leaf (-42))))) (.branch 65 (.branch 63 (.leaf (-41)) (.branch 64 (.leaf (-35)) (.leaf (-29)))) (.branch 66 (.leaf (-23)) (.branch 67 (.leaf (-17)) (.leaf (-11)))))),
  (.branch 57 (.branch 47 (.leaf (-19)) (.leaf (-18))) (.branch 67 (.leaf (-17)) (.leaf (-11)))),
  (.branch 63 (.branch 60 (.branch 48 (.leaf (-21)) (.leaf (-20))) (.branch 61 (.leaf (-18)) (.branch 62 (.leaf (-16)) (.leaf (-14))))) (.branch 65 (.branch 64 (.leaf (-12)) (.leaf (-10))) (.branch 66 (.leaf (-8)) (.branch 67 (.leaf (-6)) (.leaf (-4)))))),
  (.branch 56 (.leaf (-5)) (.leaf (-4))),
  (.branch 64 (.branch 62 (.leaf (-16)) (.branch 63 (.leaf (-14)) (.leaf (-12)))) (.branch 66 (.branch 65 (.leaf (-10)) (.leaf (-8))) (.branch 67 (.leaf (-6)) (.leaf (-4))))),
  (.branch 65 (.branch 49 (.leaf (-8)) (.branch 64 (.leaf (-7)) (.leaf (-6)))) (.branch 66 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3))))),
  (.branch 55 (.leaf (-2)) (.branch 56 (.leaf (-1)) (.leaf (0))))]
def witnessP9_288_4873 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (6))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (8))) (.branch 24 (.leaf (3)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (6))) (.branch 28 (.leaf (4)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (3))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (5)) (.leaf (7)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (4)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (6)) (.leaf (1))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (0)) (.leaf (8)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (5))) (.branch 49 (.leaf (1)) (.branch 50 (.leaf (0)) (.leaf (3))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (2)) (.leaf (4))) (.branch 54 (.leaf (6)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (1)) (.leaf (7))) (.branch 58 (.leaf (3)) (.leaf (0))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (2)) (.leaf (5))) (.branch 62 (.leaf (4)) (.leaf (1)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (3))) (.branch 66 (.leaf (2)) (.branch 67 (.leaf (6)) (.leaf (8)))))))))
  code := certificateP9_4873
  counts := ![(.branch 30 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 50 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 59 (.branch 55 (.leaf (11)) (.leaf (12))) (.branch 64 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 36 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 39 (.leaf (5)) (.branch 47 (.leaf (6)) (.leaf (7)))) (.branch 60 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 38 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 65 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 61 (.leaf (4)) (.leaf (5))))),
  (.branch 41 (.branch 14 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 54 (.leaf (3)) (.branch 67 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3)))),
  (.branch 46 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 68 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 25 (.leaf (-27)) (.leaf (-29)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-24)) (.leaf (-28)))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 52 (.leaf (-3)) (.leaf (-4)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 43 (.leaf (-5)) (.leaf (-6)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 44 (.leaf (-22)) (.leaf (-24)))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (-7))) (.branch 33 (.leaf (-8)) (.leaf (-9)))),
  (.branch 54 (.branch 27 (.leaf (0)) (.leaf (-1))) (.branch 67 (.leaf (-2)) (.leaf (-3)))),
  (.branch 12 (.leaf (0)) (.branch 34 (.leaf (-32)) (.leaf (-34)))),
  (.leaf (0))]
  high := ![(.branch 65 (.branch 60 (.leaf (-29)) (.leaf (-28))) (.branch 66 (.leaf (-21)) (.branch 67 (.leaf (-14)) (.leaf (-7))))),
  (.branch 64 (.branch 50 (.branch 43 (.leaf (-28)) (.leaf (-27))) (.branch 57 (.leaf (-26)) (.leaf (-25)))) (.branch 66 (.branch 65 (.leaf (-20)) (.leaf (-15))) (.branch 67 (.leaf (-10)) (.leaf (-5))))),
  (.branch 67 (.leaf (-4)) (.leaf (-3))),
  (.branch 66 (.branch 44 (.leaf (-6)) (.leaf (-5))) (.branch 67 (.leaf (-4)) (.leaf (-3)))),
  (.branch 64 (.branch 54 (.branch 45 (.leaf (-24)) (.leaf (-23))) (.branch 63 (.leaf (-22)) (.leaf (-19)))) (.branch 66 (.branch 65 (.leaf (-16)) (.leaf (-13))) (.branch 67 (.leaf (-10)) (.leaf (-7))))),
  (.branch 64 (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-8)) (.leaf (-7)))) (.branch 66 (.branch 65 (.leaf (-6)) (.leaf (-5))) (.branch 67 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 62 (.branch 59 (.branch 35 (.leaf (-34)) (.branch 58 (.leaf (-33)) (.leaf (-30)))) (.branch 60 (.leaf (-27)) (.branch 61 (.leaf (-24)) (.leaf (-21))))) (.branch 65 (.branch 63 (.leaf (-18)) (.branch 64 (.leaf (-15)) (.leaf (-12)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (0))]
def witnessP9_288_4874 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (4))) (.branch 11 (.leaf (8)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (5)) (.leaf (0))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (2))) (.branch 20 (.leaf (7)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (2)) (.leaf (6))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (4)) (.leaf (1))) (.branch 28 (.leaf (5)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (2))) (.branch 32 (.leaf (8)) (.branch 33 (.leaf (4)) (.leaf (1)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (3)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (4))) (.branch 41 (.leaf (0)) (.leaf (6))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (2)) (.leaf (3))) (.branch 45 (.leaf (7)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (4))) (.branch 49 (.leaf (2)) (.branch 50 (.leaf (5)) (.leaf (0))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (3)) (.leaf (1))) (.branch 54 (.leaf (8)) (.leaf (2)))) (.branch 57 (.branch 56 (.leaf (4)) (.leaf (0))) (.branch 58 (.leaf (1)) (.leaf (6))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (3)) (.leaf (2))) (.branch 62 (.leaf (5)) (.leaf (0)))) (.branch 65 (.branch 64 (.leaf (4)) (.leaf (1))) (.branch 66 (.leaf (7)) (.branch 67 (.leaf (3)) (.leaf (2)))))))))
  code := certificateP9_4874
  counts := ![(.branch 29 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 53 (.branch 39 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))) (.branch 58 (.leaf (9)) (.branch 65 (.leaf (10)) (.leaf (11)))))),
  (.branch 36 (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))) (.branch 55 (.branch 43 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))) (.branch 61 (.leaf (9)) (.branch 68 (.leaf (10)) (.leaf (11)))))),
  (.branch 37 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 44 (.leaf (5)) (.leaf (6))) (.branch 60 (.leaf (7)) (.branch 67 (.leaf (8)) (.leaf (9)))))),
  (.branch 33 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 45 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.leaf (-24))) (.branch 51 (.leaf (-31)) (.leaf (-35)))),
  (.branch 27 (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-9)) (.leaf (-10)))) (.branch 39 (.leaf (-11)) (.branch 58 (.leaf (-13)) (.leaf (-14))))),
  (.branch 36 (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4)))) (.branch 55 (.leaf (-6)) (.branch 61 (.leaf (-7)) (.leaf (-8))))),
  (.branch 6 (.leaf (0)) (.branch 44 (.leaf (-5)) (.leaf (-6)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-14))) (.branch 40 (.leaf (-16)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.branch 38 (.leaf (-15)) (.leaf (-16)))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 20 (.leaf (0)) (.branch 66 (.leaf (-4)) (.leaf (-6)))),
  (.branch 32 (.branch 11 (.leaf (0)) (.leaf (-13))) (.branch 54 (.leaf (-16)) (.leaf (-18))))]
  high := ![(.branch 64 (.branch 52 (.leaf (-35)) (.branch 58 (.leaf (-34)) (.leaf (-33)))) (.branch 66 (.branch 65 (.leaf (-28)) (.leaf (-23))) (.branch 67 (.leaf (-18)) (.leaf (-13))))),
  (.branch 66 (.branch 59 (.leaf (-14)) (.leaf (-13))) (.branch 67 (.leaf (-11)) (.leaf (-9)))),
  (.branch 63 (.branch 62 (.leaf (-8)) (.leaf (-6))) (.branch 64 (.leaf (-4)) (.branch 65 (.leaf (-2)) (.leaf (0))))),
  (.leaf (-6)),
  (.branch 57 (.branch 41 (.leaf (-18)) (.branch 49 (.leaf (-17)) (.leaf (-16)))) (.branch 66 (.branch 65 (.leaf (-15)) (.leaf (-12))) (.branch 67 (.leaf (-9)) (.leaf (-6))))),
  (.branch 64 (.branch 51 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 63 (.leaf (-14)) (.leaf (-12)))) (.branch 66 (.branch 65 (.leaf (-10)) (.leaf (-8))) (.branch 67 (.leaf (-6)) (.leaf (-4))))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 67 (.leaf (-6)) (.leaf (-5))),
  (.branch 61 (.branch 57 (.branch 55 (.leaf (-18)) (.branch 56 (.leaf (-17)) (.leaf (-16)))) (.branch 59 (.branch 58 (.leaf (-15)) (.leaf (-14))) (.branch 60 (.leaf (-13)) (.leaf (-12))))) (.branch 64 (.branch 62 (.leaf (-11)) (.branch 63 (.leaf (-10)) (.leaf (-9)))) (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-7))) (.branch 67 (.leaf (-6)) (.leaf (-5))))))]
def witnessP9_288_4875 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (4))) (.branch 11 (.leaf (6)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (5)) (.leaf (0))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (2))) (.branch 20 (.leaf (6)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (2)) (.leaf (8))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (4)) (.leaf (1))) (.branch 28 (.leaf (5)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (2))) (.branch 32 (.leaf (6)) (.branch 33 (.leaf (4)) (.leaf (1)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (3)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (4))) (.branch 41 (.leaf (0)) (.leaf (7))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (2)) (.leaf (3))) (.branch 45 (.leaf (6)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (4))) (.branch 49 (.leaf (2)) (.branch 50 (.leaf (5)) (.leaf (0))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (3)) (.leaf (1))) (.branch 54 (.leaf (6)) (.leaf (2)))) (.branch 57 (.branch 56 (.leaf (4)) (.leaf (0))) (.branch 58 (.leaf (1)) (.leaf (8))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (3)) (.leaf (2))) (.branch 62 (.leaf (5)) (.leaf (0)))) (.branch 65 (.branch 64 (.leaf (4)) (.leaf (1))) (.branch 66 (.leaf (6)) (.branch 67 (.leaf (3)) (.leaf (2)))))))))
  code := certificateP9_4875
  counts := ![(.branch 29 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 53 (.branch 39 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))) (.branch 58 (.leaf (9)) (.branch 65 (.leaf (10)) (.leaf (11)))))),
  (.branch 36 (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))) (.branch 55 (.branch 43 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))) (.branch 61 (.leaf (9)) (.branch 68 (.leaf (10)) (.leaf (11)))))),
  (.branch 37 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 44 (.leaf (5)) (.leaf (6))) (.branch 60 (.leaf (7)) (.branch 67 (.leaf (8)) (.leaf (9)))))),
  (.branch 33 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 59 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.leaf (-24))) (.branch 51 (.leaf (-31)) (.leaf (-35)))),
  (.branch 27 (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-9)) (.leaf (-10)))) (.branch 39 (.leaf (-11)) (.branch 58 (.leaf (-13)) (.leaf (-14))))),
  (.branch 36 (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4)))) (.branch 55 (.leaf (-6)) (.branch 61 (.leaf (-7)) (.leaf (-8))))),
  (.branch 6 (.leaf (0)) (.branch 44 (.leaf (-5)) (.leaf (-6)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-14))) (.branch 40 (.leaf (-16)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.branch 38 (.leaf (-15)) (.leaf (-16)))),
  (.branch 20 (.branch 11 (.leaf (0)) (.leaf (-1))) (.branch 54 (.leaf (-4)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-26))),
  (.branch 25 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 64 (.branch 52 (.leaf (-35)) (.branch 58 (.leaf (-34)) (.leaf (-33)))) (.branch 66 (.branch 65 (.leaf (-28)) (.leaf (-23))) (.branch 67 (.leaf (-18)) (.leaf (-13))))),
  (.branch 66 (.branch 59 (.leaf (-14)) (.leaf (-13))) (.branch 67 (.leaf (-11)) (.leaf (-9)))),
  (.branch 63 (.branch 62 (.leaf (-8)) (.leaf (-6))) (.branch 64 (.leaf (-4)) (.branch 65 (.leaf (-2)) (.leaf (0))))),
  (.leaf (-6)),
  (.branch 57 (.branch 41 (.leaf (-18)) (.branch 49 (.leaf (-17)) (.leaf (-16)))) (.branch 66 (.branch 65 (.leaf (-15)) (.leaf (-12))) (.branch 67 (.leaf (-9)) (.leaf (-6))))),
  (.branch 64 (.branch 51 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 63 (.leaf (-14)) (.leaf (-12)))) (.branch 66 (.branch 65 (.leaf (-10)) (.leaf (-8))) (.branch 67 (.leaf (-6)) (.leaf (-4))))),
  (.branch 67 (.leaf (-6)) (.leaf (-5))),
  (.branch 55 (.branch 48 (.branch 45 (.branch 43 (.leaf (-26)) (.branch 44 (.leaf (-25)) (.leaf (-24)))) (.branch 46 (.leaf (-23)) (.branch 47 (.leaf (-22)) (.leaf (-21))))) (.branch 51 (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-19)) (.leaf (-18)))) (.branch 53 (.branch 52 (.leaf (-17)) (.leaf (-16))) (.branch 54 (.leaf (-15)) (.leaf (-14)))))) (.branch 61 (.branch 58 (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))) (.branch 59 (.leaf (-10)) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_288_4876 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (1))) (.branch 11 (.leaf (7)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (0)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (5)) (.leaf (0))) (.branch 28 (.leaf (8)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (1)) (.leaf (3)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (6)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (1))) (.branch 41 (.leaf (3)) (.leaf (0))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (4)) (.leaf (1))) (.branch 45 (.leaf (7)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (1))) (.branch 49 (.leaf (5)) (.branch 50 (.leaf (0)) (.leaf (3))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (1)) (.leaf (0))) (.branch 54 (.leaf (4)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (2)) (.leaf (0))) (.branch 58 (.leaf (3)) (.leaf (1))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (6)) (.leaf (0))) (.branch 62 (.leaf (8)) (.leaf (1)))) (.branch 65 (.branch 64 (.leaf (2)) (.leaf (0))) (.branch 66 (.leaf (4)) (.branch 67 (.leaf (1)) (.leaf (3)))))))))
  code := certificateP9_4876
  counts := ![(.branch 31 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 50 (.branch 38 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 61 (.leaf (16)) (.branch 65 (.leaf (17)) (.leaf (18))))))),
  (.branch 33 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))) (.branch 52 (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.branch 48 (.leaf (12)) (.leaf (13))))) (.branch 59 (.branch 55 (.leaf (14)) (.leaf (15))) (.branch 63 (.leaf (16)) (.branch 67 (.leaf (17)) (.leaf (18))))))),
  (.branch 30 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 62 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 19 (.leaf (-32)) (.leaf (-33)))),
  (.branch 2 (.leaf (0)) (.leaf (-16))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (-2))) (.branch 41 (.leaf (-3)) (.branch 58 (.leaf (-4)) (.leaf (-5))))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-59))),
  (.branch 15 (.leaf (0)) (.branch 37 (.leaf (-23)) (.leaf (-25)))),
  (.branch 11 (.leaf (0)) (.leaf (-23))),
  (.branch 28 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 62 (.branch 54 (.leaf (-33)) (.branch 58 (.leaf (-31)) (.leaf (-29)))) (.branch 66 (.leaf (-27)) (.branch 67 (.leaf (-18)) (.leaf (-9))))),
  (.branch 56 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 60 (.leaf (-13)) (.branch 64 (.leaf (-11)) (.leaf (-9))))),
  (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-6))) (.branch 67 (.leaf (-4)) (.leaf (-2)))),
  (.branch 61 (.branch 59 (.leaf (-5)) (.branch 60 (.leaf (-4)) (.leaf (-3)))) (.branch 62 (.leaf (-2)) (.branch 63 (.leaf (-1)) (.leaf (0))))),
  (.branch 55 (.leaf (-8)) (.branch 67 (.leaf (-6)) (.leaf (-3)))),
  (.branch 57 (.branch 52 (.branch 27 (.branch 4 (.leaf (-59)) (.leaf (-58))) (.branch 50 (.leaf (-57)) (.branch 51 (.leaf (-54)) (.leaf (-51))))) (.branch 54 (.branch 53 (.leaf (-48)) (.leaf (-45))) (.branch 55 (.leaf (-42)) (.branch 56 (.leaf (-39)) (.leaf (-36)))))) (.branch 62 (.branch 59 (.branch 58 (.leaf (-33)) (.leaf (-30))) (.branch 60 (.leaf (-27)) (.branch 61 (.leaf (-24)) (.leaf (-21))))) (.branch 65 (.branch 63 (.leaf (-18)) (.branch 64 (.leaf (-15)) (.leaf (-12)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 63 (.branch 61 (.branch 38 (.leaf (-25)) (.leaf (-24))) (.branch 62 (.leaf (-21)) (.leaf (-18)))) (.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-12))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 56 (.branch 50 (.branch 47 (.branch 46 (.leaf (-23)) (.leaf (-22))) (.branch 48 (.leaf (-21)) (.branch 49 (.leaf (-20)) (.leaf (-19))))) (.branch 53 (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-17)) (.leaf (-16)))) (.branch 54 (.leaf (-15)) (.branch 55 (.leaf (-14)) (.leaf (-13)))))) (.branch 62 (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-11)) (.leaf (-10)))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_288_4877 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (0))) (.branch 11 (.leaf (7)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (3))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (6))) (.branch 24 (.leaf (0)) (.leaf (4))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (8)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (5)) (.leaf (3))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (2)) (.leaf (4)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (6)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (3)) (.leaf (2))) (.branch 41 (.leaf (1)) (.leaf (4))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (5)) (.leaf (0))) (.branch 45 (.leaf (7)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (3))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (6)) (.leaf (4))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (1)) (.leaf (0))) (.branch 54 (.leaf (2)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (3)) (.leaf (5))) (.branch 58 (.leaf (0)) (.leaf (4))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (2)) (.leaf (1))) (.branch 62 (.leaf (8)) (.leaf (0)))) (.branch 65 (.branch 64 (.leaf (6)) (.leaf (3))) (.branch 66 (.leaf (1)) (.branch 67 (.leaf (2)) (.leaf (4)))))))))
  code := certificateP9_4877
  counts := ![(.branch 29 (.branch 10 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 38 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 32 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))) (.branch 52 (.branch 41 (.branch 36 (.leaf (7)) (.leaf (8))) (.branch 46 (.leaf (9)) (.leaf (10)))) (.branch 61 (.branch 55 (.leaf (11)) (.leaf (12))) (.branch 66 (.leaf (13)) (.leaf (14)))))),
  (.branch 33 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 40 (.leaf (5)) (.branch 47 (.leaf (6)) (.leaf (7)))) (.branch 60 (.leaf (8)) (.branch 67 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 62 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 38 (.leaf (-6)) (.leaf (-7)))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 55 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (-4)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-53))) (.branch 43 (.leaf (-56)) (.leaf (-57)))),
  (.branch 9 (.leaf (0)) (.leaf (-23))),
  (.branch 11 (.leaf (0)) (.leaf (-23))),
  (.branch 28 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 65 (.branch 64 (.leaf (-7)) (.leaf (-6))) (.branch 66 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3))))),
  (.branch 56 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3)))),
  (.branch 61 (.leaf (-6)) (.leaf (-5))),
  (.branch 66 (.branch 57 (.leaf (-7)) (.leaf (-6))) (.branch 67 (.leaf (-4)) (.leaf (-2)))),
  (.branch 60 (.leaf (-1)) (.leaf (0))),
  (.branch 62 (.branch 59 (.branch 44 (.leaf (-57)) (.branch 58 (.leaf (-55)) (.leaf (-50)))) (.branch 60 (.leaf (-45)) (.branch 61 (.leaf (-40)) (.leaf (-35))))) (.branch 65 (.branch 63 (.leaf (-30)) (.branch 64 (.leaf (-25)) (.leaf (-20)))) (.branch 66 (.leaf (-15)) (.branch 67 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 65 (.branch 10 (.leaf (-23)) (.branch 51 (.leaf (-22)) (.leaf (-20)))) (.branch 66 (.leaf (-15)) (.branch 67 (.leaf (-10)) (.leaf (-5))))),
  (.branch 56 (.branch 50 (.branch 47 (.branch 46 (.leaf (-23)) (.leaf (-22))) (.branch 48 (.leaf (-21)) (.branch 49 (.leaf (-20)) (.leaf (-19))))) (.branch 53 (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-17)) (.leaf (-16)))) (.branch 54 (.leaf (-15)) (.branch 55 (.leaf (-14)) (.leaf (-13)))))) (.branch 62 (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-11)) (.leaf (-10)))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_288_4878 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (5)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (2)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (7)) (.branch 33 (.leaf (2)) (.leaf (3)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (5)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (3))) (.branch 41 (.leaf (1)) (.leaf (2))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (4))) (.branch 45 (.leaf (1)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (6)) (.branch 50 (.leaf (1)) (.leaf (3))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (2))) (.branch 54 (.leaf (5)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (3))) (.branch 58 (.leaf (2)) (.leaf (1))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (0)) (.leaf (4))) (.branch 62 (.leaf (2)) (.leaf (3)))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (0))) (.branch 66 (.leaf (8)) (.branch 67 (.leaf (2)) (.leaf (3)))))))))
  code := certificateP9_4878
  counts := ![(.branch 31 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 48 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 50 (.branch 41 (.branch 36 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 59 (.branch 55 (.leaf (11)) (.leaf (12))) (.branch 64 (.leaf (13)) (.leaf (14)))))),
  (.branch 33 (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))) (.branch 53 (.branch 42 (.branch 38 (.leaf (7)) (.leaf (8))) (.branch 47 (.leaf (9)) (.leaf (10)))) (.branch 62 (.branch 58 (.leaf (11)) (.leaf (12))) (.branch 67 (.leaf (13)) (.leaf (14)))))),
  (.branch 34 (.branch 17 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))) (.branch 63 (.branch 57 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2)))),
  (.branch 32 (.leaf (0)) (.leaf (1))),
  (.branch 66 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 25 (.leaf (-4)) (.branch 59 (.leaf (-5)) (.leaf (-6))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 42 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 15 (.leaf (0)) (.leaf (-19))),
  (.branch 32 (.leaf (0)) (.leaf (-36))),
  (.branch 66 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 66 (.branch 61 (.leaf (-15)) (.leaf (-12))) (.branch 67 (.leaf (-8)) (.leaf (-4)))),
  (.branch 66 (.branch 65 (.leaf (-6)) (.leaf (-5))) (.branch 67 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-3)),
  (.leaf (0)),
  (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))),
  (.branch 61 (.branch 57 (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 53 (.branch 51 (.branch 50 (.leaf (-19)) (.leaf (-18))) (.branch 52 (.leaf (-17)) (.leaf (-16)))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-14))) (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))))) (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 41 (.branch 36 (.branch 34 (.branch 33 (.leaf (-36)) (.leaf (-35))) (.branch 35 (.leaf (-34)) (.leaf (-33)))) (.branch 38 (.branch 37 (.leaf (-32)) (.leaf (-31))) (.branch 39 (.leaf (-30)) (.branch 40 (.leaf (-29)) (.leaf (-28)))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-27)) (.leaf (-26))) (.branch 44 (.leaf (-25)) (.leaf (-24)))) (.branch 47 (.branch 46 (.leaf (-23)) (.leaf (-22))) (.branch 48 (.leaf (-21)) (.branch 49 (.leaf (-20)) (.leaf (-19))))))) (.branch 59 (.branch 54 (.branch 52 (.branch 51 (.leaf (-18)) (.leaf (-17))) (.branch 53 (.leaf (-16)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-14)) (.leaf (-13))) (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-11)) (.leaf (-10)))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 67 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_288_4879 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (6))) (.branch 11 (.leaf (1)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (5)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (8))) (.branch 24 (.leaf (2)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (6))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (2)) (.leaf (7)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (5)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (3))) (.branch 41 (.leaf (1)) (.leaf (2))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (6))) (.branch 45 (.leaf (1)) (.leaf (8)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (4)) (.branch 50 (.leaf (1)) (.leaf (3))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (2))) (.branch 54 (.leaf (5)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (7))) (.branch 58 (.leaf (2)) (.leaf (1))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (0)) (.leaf (6))) (.branch 62 (.leaf (2)) (.leaf (3)))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (0))) (.branch 66 (.leaf (4)) (.branch 67 (.leaf (2)) (.leaf (8)))))))))
  code := certificateP9_4879
  counts := ![(.branch 31 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 48 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 50 (.branch 41 (.branch 36 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 59 (.branch 55 (.leaf (11)) (.leaf (12))) (.branch 64 (.leaf (13)) (.leaf (14)))))),
  (.branch 33 (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))) (.branch 53 (.branch 42 (.branch 38 (.leaf (7)) (.leaf (8))) (.branch 47 (.leaf (9)) (.leaf (10)))) (.branch 62 (.branch 58 (.leaf (11)) (.leaf (12))) (.branch 67 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 34 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3)))),
  (.branch 46 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 68 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 25 (.leaf (-4)) (.branch 59 (.leaf (-5)) (.leaf (-6))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 42 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-16)) (.leaf (-17)))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.branch 34 (.leaf (-32)) (.leaf (-34)))),
  (.leaf (0))]
  high := ![(.branch 66 (.branch 61 (.leaf (-15)) (.leaf (-12))) (.branch 67 (.leaf (-8)) (.leaf (-4)))),
  (.branch 66 (.branch 65 (.leaf (-6)) (.leaf (-5))) (.branch 67 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 65 (.branch 52 (.leaf (-17)) (.branch 64 (.leaf (-15)) (.leaf (-12)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 67 (.leaf (-2)) (.leaf (-1))),
  (.branch 61 (.branch 57 (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))),
  (.branch 62 (.branch 59 (.branch 35 (.leaf (-34)) (.branch 58 (.leaf (-33)) (.leaf (-30)))) (.branch 60 (.leaf (-27)) (.branch 61 (.leaf (-24)) (.leaf (-21))))) (.branch 65 (.branch 63 (.leaf (-18)) (.branch 64 (.leaf (-15)) (.leaf (-12)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (0))]
def witnessP9_288_4880 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (7))) (.branch 11 (.leaf (2)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (8)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (1))) (.branch 28 (.leaf (4)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (6)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (7)) (.leaf (3)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (5)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (3))) (.branch 41 (.leaf (4)) (.leaf (1))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (8))) (.branch 45 (.leaf (2)) (.leaf (6)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (3))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (4)) (.leaf (1))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (2)) (.leaf (0))) (.branch 54 (.leaf (3)) (.leaf (5)))) (.branch 57 (.branch 56 (.leaf (7)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (0))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (3)) (.leaf (1))) (.branch 62 (.leaf (4)) (.leaf (0)))) (.branch 65 (.branch 64 (.leaf (6)) (.leaf (2))) (.branch 66 (.leaf (1)) (.branch 67 (.leaf (8)) (.leaf (3)))))))))
  code := certificateP9_4880
  counts := ![(.branch 29 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 39 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 43 (.leaf (9)) (.leaf (10)))) (.branch 59 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 32 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))) (.branch 51 (.branch 42 (.branch 36 (.leaf (7)) (.leaf (8))) (.branch 47 (.leaf (9)) (.leaf (10)))) (.branch 61 (.branch 57 (.leaf (11)) (.leaf (12))) (.branch 66 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 38 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 65 (.leaf (9)) (.leaf (10)))))),
  (.branch 34 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 40 (.leaf (5)) (.branch 48 (.leaf (6)) (.leaf (7)))) (.branch 60 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 67 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 9 (.leaf (-5)) (.branch 43 (.leaf (-6)) (.leaf (-7))))),
  (.branch 2 (.leaf (0)) (.branch 36 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (-14)) (.leaf (-16)))),
  (.branch 26 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 60 (.leaf (-2)) (.leaf (-3)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 50 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-38))),
  (.branch 22 (.leaf (0)) (.branch 44 (.leaf (-2)) (.leaf (-4))))]
  high := ![(.branch 65 (.branch 64 (.leaf (-7)) (.leaf (-6))) (.branch 66 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3))))),
  (.branch 67 (.leaf (-4)) (.leaf (-3))),
  (.branch 66 (.branch 59 (.leaf (-16)) (.leaf (-15))) (.branch 67 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.branch 61 (.leaf (-3)) (.leaf (-2))) (.branch 63 (.leaf (-1)) (.leaf (0)))),
  (.branch 65 (.branch 63 (.leaf (-10)) (.branch 64 (.leaf (-9)) (.leaf (-8)))) (.branch 66 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5))))),
  (.branch 61 (.branch 57 (.branch 38 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 65 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))),
  (.branch 61 (.branch 57 (.branch 11 (.leaf (-38)) (.branch 34 (.leaf (-37)) (.leaf (-36)))) (.branch 59 (.branch 58 (.leaf (-33)) (.leaf (-30))) (.branch 60 (.leaf (-27)) (.leaf (-24))))) (.branch 64 (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 45 (.leaf (-4)) (.leaf (-3)))]
def witnessP9_288_4881 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (3))) (.branch 7 (.leaf (4)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (8))) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (3))) (.branch 15 (.leaf (7)) (.branch 16 (.leaf (4)) (.leaf (6))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (8)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (3))) (.branch 24 (.leaf (4)) (.leaf (7))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (6))) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (8)) (.leaf (3))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (4)) (.leaf (7)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (6)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (8)) (.leaf (3))) (.branch 41 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (7))) (.branch 45 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (6)) (.leaf (3))) (.branch 49 (.leaf (8)) (.branch 50 (.leaf (4)) (.leaf (5))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (7)) (.leaf (2)))) (.branch 57 (.branch 56 (.leaf (6)) (.leaf (3))) (.branch 58 (.leaf (4)) (.leaf (8))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (0)) (.leaf (5))) (.branch 62 (.leaf (1)) (.leaf (2)))) (.branch 65 (.branch 64 (.leaf (7)) (.leaf (3))) (.branch 66 (.leaf (6)) (.branch 67 (.leaf (4)) (.leaf (8)))))))))
  code := certificateP9_4881
  counts := ![(.branch 26 (.branch 9 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 67 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.leaf (7))))),
  (.branch 37 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 47 (.leaf (4)) (.leaf (5))) (.branch 66 (.leaf (6)) (.leaf (7))))),
  (.branch 34 (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 64 (.leaf (6)) (.leaf (7))))),
  (.branch 39 (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))) (.branch 59 (.branch 49 (.leaf (4)) (.leaf (5))) (.branch 68 (.leaf (6)) (.leaf (7)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-15)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 22 (.branch 3 (.leaf (0)) (.leaf (-47))) (.branch 51 (.leaf (-50)) (.leaf (-51)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-12)) (.leaf (-17)))),
  (.branch 5 (.leaf (0)) (.branch 34 (.leaf (-33)) (.leaf (-34)))),
  (.leaf (0))]
  high := ![(.branch 64 (.branch 62 (.branch 61 (.leaf (-16)) (.leaf (-14))) (.branch 63 (.leaf (-12)) (.leaf (-10)))) (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-6))) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 64 (.branch 54 (.leaf (-13)) (.branch 63 (.leaf (-12)) (.leaf (-10)))) (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-6))) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 65 (.branch 64 (.leaf (-10)) (.leaf (-8))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2)))),
  (.branch 59 (.leaf (-3)) (.leaf (-2))),
  (.branch 64 (.branch 62 (.branch 52 (.leaf (-51)) (.leaf (-49))) (.branch 63 (.leaf (-42)) (.leaf (-35)))) (.branch 66 (.branch 65 (.leaf (-28)) (.leaf (-21))) (.branch 67 (.leaf (-14)) (.leaf (-7))))),
  (.branch 57 (.branch 18 (.leaf (-17)) (.leaf (-16))) (.branch 67 (.leaf (-14)) (.leaf (-7)))),
  (.branch 55 (.branch 35 (.leaf (-34)) (.branch 45 (.leaf (-32)) (.leaf (-30)))) (.branch 66 (.branch 65 (.leaf (-28)) (.leaf (-21))) (.branch 67 (.leaf (-14)) (.leaf (-7))))),
  (.leaf (0))]
def witnessP9_288_4882 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (6))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (8)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (4)) (.leaf (7))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (3)) (.leaf (2)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (6)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (1)) (.leaf (8))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (3)) (.leaf (0))) (.branch 45 (.leaf (2)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (3)) (.leaf (2))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (1)) (.leaf (0))) (.branch 54 (.leaf (7)) (.leaf (3)))) (.branch 57 (.branch 56 (.leaf (1)) (.leaf (2))) (.branch 58 (.leaf (0)) (.leaf (6))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (3)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (0)))) (.branch 65 (.branch 64 (.leaf (4)) (.leaf (8))) (.branch 66 (.leaf (1)) (.branch 67 (.leaf (3)) (.leaf (2)))))))))
  code := certificateP9_4882
  counts := ![(.branch 29 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 39 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 32 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))) (.branch 52 (.branch 41 (.branch 36 (.leaf (7)) (.leaf (8))) (.branch 46 (.leaf (9)) (.leaf (10)))) (.branch 61 (.branch 56 (.leaf (11)) (.leaf (12))) (.branch 66 (.leaf (13)) (.leaf (14)))))),
  (.branch 34 (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 40 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 57 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 16 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 38 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 67 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 19 (.leaf (-5)) (.branch 53 (.leaf (-6)) (.leaf (-7))))),
  (.branch 2 (.leaf (0)) (.branch 36 (.leaf (-3)) (.leaf (-4)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))) (.branch 43 (.leaf (-4)) (.branch 60 (.leaf (-5)) (.leaf (-6))))),
  (.branch 13 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 25 (.leaf (-59)) (.leaf (-61)))),
  (.branch 14 (.leaf (0)) (.branch 59 (.leaf (-26)) (.leaf (-27)))),
  (.branch 8 (.leaf (0)) (.leaf (-44))),
  (.branch 20 (.leaf (0)) (.branch 42 (.leaf (-8)) (.leaf (-10))))]
  high := ![(.branch 65 (.branch 64 (.leaf (-7)) (.leaf (-6))) (.branch 66 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3))))),
  (.branch 67 (.leaf (-4)) (.leaf (-3))),
  (.branch 63 (.leaf (-1)) (.leaf (0))),
  (.branch 61 (.leaf (-6)) (.leaf (-5))),
  (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 52 (.branch 49 (.branch 26 (.leaf (-61)) (.leaf (-60))) (.branch 50 (.leaf (-57)) (.branch 51 (.leaf (-54)) (.leaf (-51))))) (.branch 54 (.branch 53 (.leaf (-48)) (.leaf (-45))) (.branch 55 (.leaf (-42)) (.branch 56 (.leaf (-39)) (.leaf (-36)))))) (.branch 62 (.branch 59 (.branch 58 (.leaf (-33)) (.leaf (-30))) (.branch 60 (.leaf (-27)) (.branch 61 (.leaf (-24)) (.leaf (-21))))) (.branch 65 (.branch 63 (.leaf (-18)) (.branch 64 (.leaf (-15)) (.leaf (-12)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-27)) (.leaf (-24))) (.branch 62 (.leaf (-21)) (.leaf (-18)))) (.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-12))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 60 (.branch 56 (.branch 32 (.branch 9 (.leaf (-44)) (.leaf (-43))) (.branch 55 (.leaf (-42)) (.leaf (-39)))) (.branch 58 (.branch 57 (.leaf (-36)) (.leaf (-33))) (.branch 59 (.leaf (-30)) (.leaf (-27))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (-24)) (.leaf (-21))) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 66 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3))))]
def witnessP9_288_4883 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (1))) (.branch 11 (.leaf (5)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (3)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (8)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (3))) (.branch 32 (.leaf (6)) (.branch 33 (.leaf (1)) (.leaf (4)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (5)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (6)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (4))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (7)) (.leaf (2))) (.branch 45 (.leaf (5)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (6)) (.branch 50 (.leaf (4)) (.leaf (2))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (3))) (.branch 54 (.leaf (5)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (6)) (.leaf (4))) (.branch 58 (.leaf (0)) (.leaf (2))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (8)) (.leaf (3))) (.branch 62 (.leaf (5)) (.leaf (1)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (4))) (.branch 66 (.leaf (6)) (.branch 67 (.leaf (2)) (.leaf (3)))))))))
  code := certificateP9_4883
  counts := ![(.branch 30 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 63 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 44 (.leaf (5)) (.leaf (6))) (.branch 59 (.leaf (7)) (.branch 67 (.leaf (8)) (.leaf (9)))))),
  (.branch 38 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 46 (.leaf (5)) (.leaf (6))) (.branch 61 (.leaf (7)) (.branch 68 (.leaf (8)) (.leaf (9)))))),
  (.branch 34 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 60 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 17 (.leaf (-50)) (.leaf (-51)))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (-14))) (.branch 36 (.leaf (-15)) (.branch 51 (.leaf (-16)) (.leaf (-17))))),
  (.leaf (0)),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (-32))) (.branch 34 (.leaf (-33)) (.leaf (-34)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 39 (.leaf (-5)) (.branch 56 (.leaf (-6)) (.leaf (-7))))),
  (.branch 9 (.leaf (0)) (.leaf (-25))),
  (.branch 26 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 65 (.branch 53 (.leaf (-14)) (.branch 59 (.leaf (-13)) (.leaf (-12)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 64 (.branch 18 (.leaf (-51)) (.branch 56 (.leaf (-49)) (.leaf (-45)))) (.branch 66 (.branch 65 (.leaf (-36)) (.leaf (-27))) (.branch 67 (.leaf (-18)) (.leaf (-9))))),
  (.branch 52 (.leaf (-17)) (.branch 60 (.leaf (-13)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 58 (.branch 35 (.leaf (-34)) (.leaf (-31))) (.branch 66 (.leaf (-27)) (.branch 67 (.leaf (-18)) (.leaf (-9))))),
  (.branch 65 (.branch 63 (.leaf (-12)) (.branch 64 (.leaf (-10)) (.leaf (-8)))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 57 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5)))),
  (.branch 55 (.branch 49 (.branch 46 (.branch 44 (.leaf (-25)) (.branch 45 (.leaf (-24)) (.leaf (-23)))) (.branch 47 (.leaf (-22)) (.branch 48 (.leaf (-21)) (.leaf (-20))))) (.branch 52 (.branch 50 (.leaf (-19)) (.branch 51 (.leaf (-18)) (.leaf (-17)))) (.branch 53 (.leaf (-16)) (.branch 54 (.leaf (-15)) (.leaf (-14)))))) (.branch 61 (.branch 58 (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))) (.branch 59 (.leaf (-10)) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 64 (.branch 62 (.branch 61 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_288_4884 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (8))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (5)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (3))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (7)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (6)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (4))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (3)) (.leaf (2)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (5)) (.leaf (8)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (1)) (.leaf (3))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (4)) (.leaf (0))) (.branch 45 (.leaf (2)) (.leaf (6)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (7))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (3)) (.leaf (2))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (1)) (.leaf (0))) (.branch 54 (.leaf (5)) (.leaf (4)))) (.branch 57 (.branch 56 (.leaf (1)) (.leaf (2))) (.branch 58 (.leaf (0)) (.leaf (3))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (8)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (6)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (4))) (.branch 66 (.leaf (1)) (.branch 67 (.leaf (3)) (.leaf (2)))))))))
  code := certificateP9_4884
  counts := ![(.branch 30 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 39 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 64 (.leaf (13)) (.leaf (14)))))),
  (.branch 32 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))) (.branch 52 (.branch 41 (.branch 36 (.leaf (7)) (.leaf (8))) (.branch 47 (.leaf (9)) (.leaf (10)))) (.branch 61 (.branch 56 (.leaf (11)) (.leaf (12))) (.branch 66 (.leaf (13)) (.leaf (14)))))),
  (.branch 34 (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 40 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 57 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 67 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 19 (.leaf (-5)) (.branch 53 (.leaf (-6)) (.leaf (-7))))),
  (.branch 2 (.leaf (0)) (.branch 36 (.leaf (-3)) (.leaf (-4)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 31 (.branch 9 (.leaf (0)) (.leaf (-5))) (.branch 65 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 26 (.branch 4 (.leaf (0)) (.leaf (-19))) (.branch 48 (.leaf (-20)) (.leaf (-21)))),
  (.branch 14 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 65 (.branch 59 (.leaf (-7)) (.leaf (-6))) (.branch 66 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3))))),
  (.branch 67 (.leaf (-4)) (.leaf (-3))),
  (.branch 63 (.leaf (-1)) (.leaf (0))),
  (.leaf (-2)),
  (.branch 66 (.leaf (-8)) (.branch 67 (.leaf (-6)) (.leaf (-4)))),
  (.branch 61 (.branch 57 (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 53 (.branch 50 (.branch 49 (.leaf (-21)) (.leaf (-20))) (.branch 51 (.leaf (-19)) (.branch 52 (.leaf (-18)) (.leaf (-17))))) (.branch 55 (.branch 54 (.leaf (-16)) (.leaf (-15))) (.branch 56 (.leaf (-14)) (.branch 57 (.leaf (-13)) (.leaf (-12)))))) (.branch 63 (.branch 60 (.branch 59 (.leaf (-11)) (.leaf (-10))) (.branch 61 (.leaf (-9)) (.branch 62 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 64 (.leaf (-6)) (.leaf (-5))) (.branch 66 (.leaf (-4)) (.branch 67 (.leaf (-3)) (.leaf (-2))))))),
  (.branch 64 (.branch 62 (.branch 61 (.leaf (-9)) (.leaf (-8))) (.branch 63 (.leaf (-7)) (.leaf (-6)))) (.branch 66 (.branch 65 (.leaf (-5)) (.leaf (-4))) (.branch 67 (.leaf (-3)) (.leaf (-2)))))]
def witnessP9_288_4885 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (6)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (7)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (6)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (8))) (.branch 24 (.leaf (4)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (5)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (7)) (.leaf (2)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (6)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (5))) (.branch 41 (.leaf (4)) (.leaf (0))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (2)) (.leaf (1))) (.branch 45 (.leaf (8)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (5)) (.leaf (2))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (6)) (.leaf (3)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (7))) (.branch 58 (.leaf (4)) (.leaf (0))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (2)) (.leaf (1))) (.branch 62 (.leaf (5)) (.leaf (0)))) (.branch 65 (.branch 64 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (8)) (.leaf (2)))))))))
  code := certificateP9_4885
  counts := ![(.branch 32 (.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))) (.branch 49 (.branch 39 (.branch 35 (.leaf (10)) (.leaf (11))) (.branch 42 (.leaf (12)) (.branch 46 (.leaf (13)) (.leaf (14))))) (.branch 59 (.branch 52 (.leaf (15)) (.branch 56 (.leaf (16)) (.leaf (17)))) (.branch 63 (.leaf (18)) (.branch 66 (.leaf (19)) (.leaf (20))))))),
  (.branch 27 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3)))),
  (.branch 45 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 67 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-12))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 31 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-2)) (.leaf (-4)))) (.branch 48 (.leaf (-5)) (.branch 65 (.leaf (-6)) (.leaf (-7))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (-11))) (.branch 50 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 11 (.leaf (0)) (.branch 33 (.leaf (-12)) (.leaf (-13)))),
  (.branch 45 (.leaf (0)) (.branch 67 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 60 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 67 (.leaf (-10)) (.leaf (-5)))),
  (.branch 64 (.branch 62 (.leaf (-14)) (.branch 63 (.leaf (-12)) (.leaf (-10)))) (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-6))) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 65 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 66 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5)))),
  (.branch 64 (.branch 51 (.leaf (-15)) (.branch 63 (.leaf (-14)) (.leaf (-12)))) (.branch 66 (.branch 65 (.leaf (-10)) (.leaf (-8))) (.branch 67 (.leaf (-6)) (.leaf (-4))))),
  (.branch 61 (.branch 57 (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 62 (.branch 59 (.branch 34 (.leaf (-13)) (.branch 58 (.leaf (-12)) (.leaf (-11)))) (.branch 60 (.leaf (-10)) (.branch 61 (.leaf (-9)) (.leaf (-8))))) (.branch 65 (.branch 63 (.leaf (-7)) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.leaf (-4)) (.branch 67 (.leaf (-3)) (.leaf (-2)))))),
  (.leaf (-2))]
def witnessP9_288_4886 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (6)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (8)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (5)) (.leaf (7))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (1)) (.leaf (2))) (.branch 28 (.leaf (0)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (8))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (4)) (.leaf (2)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (6)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (3)) (.leaf (1))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (7)) (.leaf (0))) (.branch 45 (.leaf (4)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (8)) (.branch 50 (.leaf (1)) (.leaf (3))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (5)) (.leaf (0))) (.branch 54 (.leaf (2)) (.leaf (6)))) (.branch 57 (.branch 56 (.leaf (1)) (.leaf (0))) (.branch 58 (.leaf (4)) (.leaf (7))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (1)) (.leaf (2))) (.branch 62 (.leaf (0)) (.leaf (3)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (8))) (.branch 66 (.leaf (1)) (.branch 67 (.leaf (5)) (.leaf (2)))))))))
  code := certificateP9_4886
  counts := ![(.branch 30 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 48 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 57 (.branch 53 (.leaf (12)) (.leaf (13))) (.branch 62 (.leaf (14)) (.branch 64 (.leaf (15)) (.leaf (16))))))),
  (.branch 32 (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 50 (.branch 42 (.branch 36 (.leaf (7)) (.leaf (8))) (.branch 46 (.leaf (9)) (.leaf (10)))) (.branch 60 (.branch 56 (.leaf (11)) (.leaf (12))) (.branch 66 (.leaf (13)) (.leaf (14)))))),
  (.branch 34 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 40 (.leaf (5)) (.branch 47 (.leaf (6)) (.leaf (7)))) (.branch 61 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 67 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-24))) (.branch 30 (.leaf (-27)) (.branch 64 (.leaf (-38)) (.leaf (-48))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 50 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (-9))) (.branch 51 (.leaf (-12)) (.leaf (-13)))),
  (.branch 45 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 58 (.leaf (-11)) (.leaf (-12)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (-8)) (.leaf (-9)))),
  (.branch 15 (.leaf (0)) (.branch 31 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 66 (.branch 65 (.leaf (-48)) (.leaf (-41))) (.branch 67 (.leaf (-34)) (.leaf (-27)))),
  (.branch 61 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3)))),
  (.branch 48 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.branch 62 (.leaf (-1)) (.leaf (0))))),
  (.branch 65 (.branch 52 (.leaf (-13)) (.branch 64 (.leaf (-12)) (.leaf (-10)))) (.branch 66 (.leaf (-8)) (.branch 67 (.leaf (-6)) (.leaf (-4))))),
  (.branch 63 (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-11))) (.branch 61 (.leaf (-10)) (.branch 62 (.leaf (-9)) (.leaf (-8))))) (.branch 65 (.branch 64 (.leaf (-7)) (.leaf (-6))) (.branch 66 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 61 (.branch 57 (.branch 38 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_288_4887 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (7)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (2))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (1))) (.branch 11 (.leaf (6)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (2))) (.branch 15 (.leaf (8)) (.branch 16 (.leaf (0)) (.leaf (5))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (5))) (.branch 24 (.leaf (0)) (.leaf (4))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (7)) (.leaf (1))) (.branch 28 (.leaf (0)) (.leaf (6)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (2))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (5)) (.leaf (4)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (8)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (3)) (.leaf (2))) (.branch 41 (.leaf (5)) (.leaf (0))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (4)) (.leaf (1))) (.branch 45 (.leaf (6)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (3)) (.leaf (2))) (.branch 49 (.leaf (7)) (.branch 50 (.leaf (0)) (.leaf (5))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (4)) (.leaf (1))) (.branch 54 (.leaf (0)) (.leaf (3)))) (.branch 57 (.branch 56 (.leaf (2)) (.leaf (5))) (.branch 58 (.leaf (0)) (.leaf (4))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (8)) (.leaf (1))) (.branch 62 (.leaf (0)) (.leaf (6)))) (.branch 65 (.branch 64 (.leaf (3)) (.leaf (2))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (5)) (.leaf (4)))))))))
  code := certificateP9_4887
  counts := ![(.branch 32 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 50 (.branch 38 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 58 (.branch 54 (.leaf (14)) (.leaf (15))) (.branch 62 (.leaf (16)) (.branch 66 (.leaf (17)) (.leaf (18))))))),
  (.branch 27 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 67 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-20))) (.branch 38 (.leaf (-26)) (.leaf (-31)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-5))) (.branch 22 (.leaf (-6)) (.leaf (-7)))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 21 (.leaf (-8)) (.leaf (-9)))),
  (.branch 25 (.leaf (0)) (.branch 59 (.leaf (-3)) (.leaf (-5)))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (-2))) (.branch 57 (.leaf (-4)) (.leaf (-6)))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-59))),
  (.branch 15 (.leaf (0)) (.branch 37 (.leaf (-23)) (.leaf (-25))))]
  high := ![(.branch 51 (.branch 43 (.branch 39 (.leaf (-31)) (.leaf (-30))) (.branch 47 (.leaf (-29)) (.leaf (-28)))) (.branch 59 (.branch 55 (.leaf (-27)) (.leaf (-26))) (.branch 63 (.leaf (-25)) (.branch 67 (.leaf (-24)) (.leaf (-17)))))),
  (.branch 64 (.branch 62 (.leaf (-14)) (.branch 63 (.leaf (-12)) (.leaf (-10)))) (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-6))) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 66 (.branch 57 (.leaf (-7)) (.leaf (-6))) (.branch 67 (.leaf (-4)) (.leaf (-2)))),
  (.branch 65 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 60 (.leaf (-5)) (.branch 61 (.leaf (-2)) (.leaf (0)))),
  (.branch 58 (.leaf (-6)) (.leaf (-5))),
  (.branch 65 (.branch 46 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))),
  (.branch 57 (.branch 52 (.branch 27 (.branch 4 (.leaf (-59)) (.leaf (-58))) (.branch 50 (.leaf (-57)) (.branch 51 (.leaf (-54)) (.leaf (-51))))) (.branch 54 (.branch 53 (.leaf (-48)) (.leaf (-45))) (.branch 55 (.leaf (-42)) (.branch 56 (.leaf (-39)) (.leaf (-36)))))) (.branch 62 (.branch 59 (.branch 58 (.leaf (-33)) (.leaf (-30))) (.branch 60 (.leaf (-27)) (.branch 61 (.leaf (-24)) (.leaf (-21))))) (.branch 65 (.branch 63 (.leaf (-18)) (.branch 64 (.leaf (-15)) (.leaf (-12)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 63 (.branch 61 (.branch 38 (.leaf (-25)) (.leaf (-24))) (.branch 62 (.leaf (-21)) (.leaf (-18)))) (.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-12))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))))]
def witnessP9_288_4888 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (7)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (8))) (.branch 11 (.leaf (1)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (1)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (7)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (2)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (8))) (.branch 28 (.leaf (3)) (.leaf (4)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (6)) (.branch 33 (.leaf (2)) (.leaf (5)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (7)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (4))) (.branch 41 (.leaf (1)) (.leaf (2))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (8))) (.branch 45 (.leaf (1)) (.leaf (5)))) (.branch 48 (.branch 47 (.leaf (3)) (.leaf (0))) (.branch 49 (.leaf (6)) (.branch 50 (.leaf (1)) (.leaf (4))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (2))) (.branch 54 (.leaf (7)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (5))) (.branch 58 (.leaf (3)) (.leaf (1))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (0)) (.leaf (8))) (.branch 62 (.leaf (2)) (.leaf (4)))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (0))) (.branch 66 (.leaf (6)) (.branch 67 (.leaf (3)) (.leaf (5)))))))))
  code := certificateP9_4888
  counts := ![(.branch 31 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 48 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 50 (.branch 41 (.branch 36 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 59 (.branch 55 (.leaf (11)) (.leaf (12))) (.branch 64 (.leaf (13)) (.leaf (14)))))),
  (.branch 33 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.leaf (7))))),
  (.branch 38 (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 58 (.branch 47 (.leaf (4)) (.leaf (5))) (.branch 67 (.leaf (6)) (.leaf (7))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 12 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 25 (.leaf (-4)) (.branch 59 (.leaf (-5)) (.leaf (-6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-6))) (.branch 42 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.branch 47 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-16)) (.leaf (-17)))),
  (.leaf (0)),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 10 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 66 (.branch 61 (.leaf (-15)) (.leaf (-12))) (.branch 67 (.leaf (-8)) (.leaf (-4)))),
  (.branch 66 (.branch 65 (.leaf (-6)) (.leaf (-5))) (.branch 67 (.leaf (-4)) (.leaf (-3)))),
  (.branch 65 (.branch 63 (.leaf (-8)) (.branch 64 (.leaf (-7)) (.leaf (-6)))) (.branch 66 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 65 (.branch 52 (.leaf (-17)) (.branch 64 (.leaf (-15)) (.leaf (-12)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 67 (.leaf (-2)) (.leaf (-1))),
  (.branch 61 (.branch 57 (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_288_4889 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (8)) (.branch 16 (.leaf (2)) (.leaf (0))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (7)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (6)) (.leaf (1))) (.branch 28 (.leaf (0)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (8))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (4)) (.leaf (1)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (0)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (7)) (.leaf (1))) (.branch 41 (.leaf (3)) (.leaf (0))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (6)) (.leaf (2))) (.branch 45 (.leaf (0)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (8)) (.branch 50 (.leaf (2)) (.leaf (0))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (3)) (.leaf (5))) (.branch 54 (.leaf (1)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (7)) (.leaf (2))) (.branch 58 (.leaf (0)) (.leaf (4))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (6)) (.leaf (1))) (.branch 62 (.leaf (0)) (.leaf (3)))) (.branch 65 (.branch 64 (.leaf (2)) (.leaf (8))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (5)) (.leaf (1)))))))))
  code := certificateP9_4889
  counts := ![(.branch 32 (.branch 14 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))))) (.branch 48 (.branch 37 (.branch 35 (.leaf (10)) (.leaf (11))) (.branch 42 (.leaf (12)) (.branch 45 (.leaf (13)) (.leaf (14))))) (.branch 58 (.branch 51 (.leaf (15)) (.branch 55 (.leaf (16)) (.leaf (17)))) (.branch 62 (.leaf (18)) (.branch 66 (.leaf (19)) (.leaf (20))))))),
  (.branch 34 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 40 (.leaf (5)) (.branch 47 (.leaf (6)) (.leaf (7)))) (.branch 61 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 36 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 4 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 53 (.leaf (3)) (.branch 67 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 24 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 14 (.leaf (-5)) (.branch 17 (.leaf (-6)) (.leaf (-7))))) (.branch 48 (.branch 35 (.leaf (-8)) (.branch 37 (.leaf (-9)) (.leaf (-11)))) (.branch 51 (.leaf (-12)) (.branch 58 (.leaf (-13)) (.leaf (-14)))))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.branch 36 (.leaf (-5)) (.leaf (-6)))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (-13))) (.branch 29 (.leaf (-14)) (.leaf (-15)))),
  (.branch 4 (.leaf (0)) (.branch 59 (.leaf (-10)) (.leaf (-11)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (-2))) (.branch 38 (.leaf (-3)) (.leaf (-4)))),
  (.branch 9 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.branch 31 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 67 (.leaf (-14)) (.leaf (-13))),
  (.branch 48 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.branch 62 (.leaf (-1)) (.leaf (0))))),
  (.branch 66 (.branch 65 (.leaf (-6)) (.leaf (-5))) (.branch 67 (.leaf (-4)) (.leaf (-3)))),
  (.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-12))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-11)) (.leaf (-10))) (.branch 62 (.leaf (-9)) (.leaf (-8)))) (.branch 65 (.branch 64 (.leaf (-7)) (.leaf (-6))) (.branch 66 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 39 (.leaf (-4)) (.leaf (-3))),
  (.branch 64 (.branch 62 (.branch 61 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))),
  (.branch 62 (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-11)) (.leaf (-10)))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_288_4890 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (7))) (.branch 11 (.leaf (4)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (3)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (8)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (1)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (4)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (1)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (1)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (5))) (.branch 41 (.leaf (1)) (.leaf (2))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (8))) (.branch 45 (.leaf (4)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (2))) (.branch 49 (.leaf (6)) (.branch 50 (.leaf (3)) (.leaf (1))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (2))) (.branch 54 (.leaf (1)) (.leaf (7)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (5))) (.branch 58 (.leaf (1)) (.leaf (2))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (0)) (.leaf (3))) (.branch 62 (.leaf (4)) (.leaf (1)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (2))) (.branch 66 (.leaf (6)) (.branch 67 (.leaf (8)) (.leaf (1)))))))))
  code := certificateP9_4890
  counts := ![(.branch 30 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.branch 64 (.leaf (15)) (.leaf (16))))))),
  (.branch 34 (.branch 17 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 51 (.branch 41 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 58 (.branch 54 (.leaf (12)) (.leaf (13))) (.branch 63 (.leaf (14)) (.branch 68 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 67 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 13 (.leaf (-15)) (.leaf (-16))))),
  (.branch 24 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 20 (.leaf (-4)) (.leaf (-5)))) (.branch 41 (.branch 37 (.leaf (-6)) (.leaf (-7))) (.branch 54 (.leaf (-8)) (.branch 58 (.leaf (-9)) (.leaf (-10)))))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.leaf (-22))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.branch 55 (.leaf (-38)) (.leaf (-39)))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 66 (.branch 65 (.leaf (-16)) (.leaf (-12))) (.branch 67 (.leaf (-8)) (.leaf (-4)))),
  (.branch 65 (.branch 59 (.leaf (-10)) (.branch 64 (.leaf (-9)) (.leaf (-7)))) (.branch 66 (.leaf (-5)) (.branch 67 (.leaf (-3)) (.leaf (-1))))),
  (.branch 60 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 64 (.branch 62 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))),
  (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 67 (.leaf (-2)) (.leaf (-1))),
  (.branch 61 (.branch 58 (.branch 56 (.leaf (-39)) (.branch 57 (.leaf (-36)) (.leaf (-33)))) (.branch 59 (.leaf (-30)) (.branch 60 (.leaf (-27)) (.leaf (-24))))) (.branch 64 (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 22 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (-3))))]
def witnessP9_288_4891 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (8)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (7)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (5)) (.leaf (1)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (1)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (3))) (.branch 41 (.leaf (1)) (.leaf (2))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (6))) (.branch 45 (.leaf (8)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (2))) (.branch 49 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (1))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (2))) (.branch 54 (.leaf (1)) (.leaf (5)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (3))) (.branch 58 (.leaf (1)) (.leaf (2))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (0)) (.leaf (4))) (.branch 62 (.leaf (7)) (.leaf (1)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (2))) (.branch 66 (.leaf (3)) (.branch 67 (.leaf (6)) (.leaf (1)))))))))
  code := certificateP9_4891
  counts := ![(.branch 30 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.branch 64 (.leaf (15)) (.leaf (16))))))),
  (.branch 34 (.branch 17 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 51 (.branch 41 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 58 (.branch 54 (.leaf (12)) (.leaf (13))) (.branch 63 (.leaf (14)) (.branch 68 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 67 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.leaf (0)) (.branch 62 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 13 (.leaf (-15)) (.leaf (-16))))),
  (.branch 24 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 20 (.leaf (-4)) (.leaf (-5)))) (.branch 41 (.branch 37 (.leaf (-6)) (.leaf (-7))) (.branch 54 (.leaf (-8)) (.branch 58 (.leaf (-9)) (.leaf (-10)))))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-22))),
  (.branch 10 (.leaf (0)) (.branch 55 (.leaf (-38)) (.leaf (-39)))),
  (.branch 21 (.leaf (0)) (.leaf (-5))),
  (.branch 28 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.leaf (-23)))]
  high := ![(.branch 66 (.branch 65 (.leaf (-16)) (.leaf (-12))) (.branch 67 (.leaf (-8)) (.leaf (-4)))),
  (.branch 65 (.branch 59 (.leaf (-10)) (.branch 64 (.leaf (-9)) (.leaf (-7)))) (.branch 66 (.leaf (-5)) (.branch 67 (.leaf (-3)) (.leaf (-1))))),
  (.branch 60 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 58 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-2)))),
  (.branch 64 (.branch 62 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.branch 58 (.branch 56 (.leaf (-39)) (.branch 57 (.leaf (-36)) (.leaf (-33)))) (.branch 59 (.leaf (-30)) (.branch 60 (.leaf (-27)) (.leaf (-24))))) (.branch 64 (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 22 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (-3)))),
  (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 50 (.branch 47 (.branch 46 (.leaf (-23)) (.leaf (-22))) (.branch 48 (.leaf (-21)) (.branch 49 (.leaf (-20)) (.leaf (-19))))) (.branch 53 (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-17)) (.leaf (-16)))) (.branch 54 (.leaf (-15)) (.branch 55 (.leaf (-14)) (.leaf (-13)))))) (.branch 62 (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-11)) (.leaf (-10)))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_288_4892 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (6)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (2)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (8))) (.branch 24 (.leaf (6)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (1)) (.leaf (7)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (1)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (3))) (.branch 41 (.leaf (6)) (.leaf (1))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (5))) (.branch 45 (.leaf (2)) (.leaf (8)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (4)) (.branch 50 (.leaf (1)) (.leaf (3))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (2))) (.branch 54 (.leaf (1)) (.leaf (5)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (7))) (.branch 58 (.leaf (6)) (.leaf (1))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (0)) (.leaf (4))) (.branch 62 (.leaf (2)) (.leaf (3)))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (0))) (.branch 66 (.leaf (5)) (.branch 67 (.leaf (1)) (.leaf (8)))))))))
  code := certificateP9_4892
  counts := ![(.branch 31 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 48 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 33 (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))) (.branch 50 (.branch 42 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 47 (.leaf (10)) (.leaf (11)))) (.branch 59 (.branch 54 (.leaf (12)) (.leaf (13))) (.branch 64 (.leaf (14)) (.branch 67 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 34 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3)))),
  (.branch 46 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 68 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 33 (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 20 (.leaf (-4)) (.leaf (-5)))) (.branch 50 (.branch 37 (.leaf (-6)) (.leaf (-7))) (.branch 54 (.leaf (-8)) (.branch 67 (.leaf (-9)) (.leaf (-10)))))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-16)) (.leaf (-17)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-22)) (.leaf (-23)))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (-4))) (.branch 32 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 12 (.leaf (0)) (.branch 34 (.leaf (-32)) (.leaf (-34)))),
  (.leaf (0))]
  high := ![(.branch 66 (.branch 61 (.leaf (-15)) (.leaf (-12))) (.branch 67 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-10)),
  (.branch 64 (.branch 54 (.leaf (-13)) (.branch 63 (.leaf (-12)) (.leaf (-10)))) (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-6))) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 65 (.branch 52 (.leaf (-17)) (.branch 64 (.leaf (-15)) (.leaf (-12)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 64 (.branch 62 (.branch 50 (.leaf (-23)) (.leaf (-21))) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 67 (.leaf (-6)) (.leaf (-3))),
  (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 62 (.branch 59 (.branch 35 (.leaf (-34)) (.branch 58 (.leaf (-33)) (.leaf (-30)))) (.branch 60 (.leaf (-27)) (.branch 61 (.leaf (-24)) (.leaf (-21))))) (.branch 65 (.branch 63 (.leaf (-18)) (.branch 64 (.leaf (-15)) (.leaf (-12)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (0))]
def witnessP9_288_4893 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (6))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (7)) (.leaf (0))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (1)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (6)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (8)) (.leaf (1))) (.branch 24 (.leaf (3)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (4)) (.leaf (7))) (.branch 28 (.leaf (2)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (6)) (.leaf (4)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (1)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (8)) (.leaf (7))) (.branch 41 (.leaf (3)) (.leaf (0))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (4)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (5)))) (.branch 48 (.branch 47 (.leaf (6)) (.leaf (0))) (.branch 49 (.leaf (3)) (.branch 50 (.leaf (1)) (.leaf (4))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (2))) (.branch 54 (.leaf (7)) (.leaf (5)))) (.branch 57 (.branch 56 (.leaf (8)) (.leaf (1))) (.branch 58 (.leaf (3)) (.leaf (0))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (4)) (.leaf (6))) (.branch 62 (.leaf (2)) (.leaf (5)))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (0))) (.branch 66 (.leaf (3)) (.branch 67 (.leaf (7)) (.leaf (4)))))))))
  code := certificateP9_4893
  counts := ![(.branch 31 (.branch 14 (.branch 1 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 35 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 61 (.leaf (4)) (.leaf (5))))),
  (.branch 40 (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 54 (.leaf (3)) (.branch 67 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 35 (.leaf (-6)) (.branch 52 (.leaf (-7)) (.leaf (-8))))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-19)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.branch 33 (.leaf (-38)) (.leaf (-39)))),
  (.branch 40 (.branch 13 (.leaf (0)) (.leaf (-3))) (.branch 67 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 66 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 67 (.leaf (-6)) (.leaf (-5)))),
  (.branch 65 (.branch 51 (.leaf (-22)) (.branch 58 (.leaf (-21)) (.leaf (-20)))) (.branch 66 (.leaf (-15)) (.branch 67 (.leaf (-10)) (.leaf (-5))))),
  (.branch 64 (.branch 54 (.leaf (-13)) (.branch 63 (.leaf (-12)) (.leaf (-10)))) (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-6))) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 67 (.leaf (-4)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 65 (.branch 64 (.leaf (-10)) (.leaf (-8))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 63 (.branch 48 (.branch 34 (.leaf (-39)) (.leaf (-37))) (.branch 62 (.leaf (-35)) (.leaf (-30)))) (.branch 65 (.branch 64 (.leaf (-25)) (.leaf (-20))) (.branch 66 (.leaf (-15)) (.branch 67 (.leaf (-10)) (.leaf (-5)))))),
  (.leaf (-5)),
  (.branch 62 (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-11)) (.leaf (-10)))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_288_4894 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (6))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (2))) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (1))) (.branch 24 (.leaf (4)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (5))) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (1)) (.leaf (7)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (3)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (5)) (.leaf (0))) (.branch 41 (.leaf (4)) (.leaf (2))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (1)) (.leaf (5))) (.branch 45 (.leaf (0)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (2))) (.branch 49 (.leaf (4)) (.branch 50 (.leaf (0)) (.leaf (6))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (1)) (.leaf (2))) (.branch 54 (.leaf (3)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (5)) (.leaf (1))) (.branch 58 (.leaf (4)) (.leaf (2))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (0)) (.leaf (5))) (.branch 62 (.leaf (1)) (.leaf (3)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (2))) (.branch 66 (.leaf (4)) (.branch 67 (.leaf (1)) (.leaf (8)))))))))
  code := certificateP9_4894
  counts := ![(.branch 30 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 50 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 60 (.branch 55 (.leaf (11)) (.leaf (12))) (.branch 64 (.leaf (13)) (.leaf (14)))))),
  (.branch 33 (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))) (.branch 52 (.branch 43 (.branch 38 (.leaf (7)) (.leaf (8))) (.branch 47 (.leaf (9)) (.leaf (10)))) (.branch 62 (.branch 57 (.leaf (11)) (.leaf (12))) (.branch 67 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2)))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 68 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 30 (.leaf (-27)) (.leaf (-28)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-6)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-4)))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-6)) (.leaf (-12)))) (.branch 44 (.leaf (-17)) (.branch 61 (.leaf (-22)) (.leaf (-27))))),
  (.branch 17 (.leaf (0)) (.leaf (-17))),
  (.branch 34 (.leaf (0)) (.leaf (-34))),
  (.leaf (0))]
  high := ![(.branch 66 (.branch 65 (.leaf (-28)) (.leaf (-21))) (.branch 67 (.leaf (-14)) (.leaf (-7)))),
  (.branch 53 (.branch 48 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 63 (.leaf (-8)) (.leaf (-7))))),
  (.branch 60 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 65 (.branch 55 (.leaf (-11)) (.branch 64 (.leaf (-10)) (.leaf (-8)))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 67 (.leaf (-4)) (.leaf (-2))),
  (.branch 64 (.branch 62 (.leaf (-27)) (.branch 63 (.leaf (-26)) (.leaf (-25)))) (.branch 66 (.branch 65 (.leaf (-24)) (.leaf (-23))) (.branch 67 (.leaf (-22)) (.leaf (-21))))),
  (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (-17)) (.leaf (-16))) (.branch 54 (.leaf (-15)) (.leaf (-14)))) (.branch 57 (.branch 56 (.leaf (-13)) (.leaf (-12))) (.branch 58 (.leaf (-11)) (.leaf (-10))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (-34)) (.leaf (-33))) (.branch 37 (.leaf (-32)) (.leaf (-31)))) (.branch 40 (.branch 39 (.leaf (-30)) (.leaf (-29))) (.branch 41 (.leaf (-28)) (.leaf (-27))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-26)) (.leaf (-25))) (.branch 45 (.leaf (-24)) (.leaf (-23)))) (.branch 48 (.branch 47 (.leaf (-22)) (.leaf (-21))) (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-19)) (.leaf (-18))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (-17)) (.leaf (-16))) (.branch 54 (.leaf (-15)) (.leaf (-14)))) (.branch 57 (.branch 56 (.leaf (-13)) (.leaf (-12))) (.branch 58 (.leaf (-11)) (.leaf (-10))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.leaf (0))]
def witnessP9_288 : Fin 44 → CycleWitness 9 := ![witnessP9_288_4851, witnessP9_288_4852, witnessP9_288_4853, witnessP9_288_4854, witnessP9_288_4855, witnessP9_288_4856, witnessP9_288_4857, witnessP9_288_4858, witnessP9_288_4859, witnessP9_288_4860, witnessP9_288_4861, witnessP9_288_4862, witnessP9_288_4863, witnessP9_288_4864, witnessP9_288_4865, witnessP9_288_4866, witnessP9_288_4867, witnessP9_288_4868, witnessP9_288_4869, witnessP9_288_4870, witnessP9_288_4871, witnessP9_288_4872, witnessP9_288_4873, witnessP9_288_4874, witnessP9_288_4875, witnessP9_288_4876, witnessP9_288_4877, witnessP9_288_4878, witnessP9_288_4879, witnessP9_288_4880, witnessP9_288_4881, witnessP9_288_4882, witnessP9_288_4883, witnessP9_288_4884, witnessP9_288_4885, witnessP9_288_4886, witnessP9_288_4887, witnessP9_288_4888, witnessP9_288_4889, witnessP9_288_4890, witnessP9_288_4891, witnessP9_288_4892, witnessP9_288_4893, witnessP9_288_4894]
end RealPinwheel.FiveSixths


