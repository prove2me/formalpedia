-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_290
-- name    : RealPinwheel_FiveSixths_WitnessP9_290
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:18:39.856824+00:00
-- url     : https://prove2.me/theorems/32cae4c0-a0bd-4857-acda-41fe610f0cd3
-- title:
--   Exact witness block P9_290
-- statement:
--   These exact witnesses represent words 4941 through 4985 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 4941–4985; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_290_4940 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (7)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (1)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (6))) (.branch 15 (.leaf (3)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (5)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (4))) (.branch 23 (.leaf (8)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (3))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (6)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (5)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (7)) (.leaf (6))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (2))) (.branch 44 (.leaf (1)) (.leaf (4)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (5))) (.branch 48 (.leaf (3)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (2))) (.branch 52 (.leaf (6)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (4))) (.branch 56 (.leaf (8)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (1)) (.leaf (3))) (.branch 60 (.leaf (2)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (5)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (6)) (.leaf (4)))))))))
  code := certificateP9_4940
  counts := ![(.branch 31 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 50 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 61 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 30 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 39 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 27 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 12 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 62 (.leaf (4)) (.leaf (5))))),
  (.branch 41 (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 65 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.branch 56 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 34 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-19)) (.leaf (-24)))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-11)) (.leaf (-14)))) (.branch 43 (.leaf (-15)) (.branch 51 (.leaf (-16)) (.leaf (-17))))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (-13))) (.branch 32 (.leaf (-20)) (.leaf (-23)))),
  (.branch 41 (.branch 14 (.leaf (0)) (.leaf (-1))) (.branch 52 (.leaf (-5)) (.branch 65 (.leaf (-12)) (.leaf (-15))))),
  (.branch 7 (.leaf (0)) (.leaf (-26))),
  (.branch 23 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 65 (.leaf (-14)) (.leaf (-10))),
  (.branch 59 (.branch 40 (.leaf (-24)) (.leaf (-23))) (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-14)) (.leaf (-7))))),
  (.branch 62 (.branch 52 (.leaf (-17)) (.branch 61 (.leaf (-16)) (.leaf (-14)))) (.branch 64 (.branch 63 (.leaf (-12)) (.leaf (-10))) (.branch 65 (.leaf (-8)) (.leaf (-6))))),
  (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 63 (.branch 33 (.leaf (-23)) (.branch 48 (.leaf (-22)) (.leaf (-21)))) (.branch 64 (.leaf (-19)) (.branch 65 (.leaf (-17)) (.leaf (-15))))),
  (.leaf (-15)),
  (.branch 53 (.branch 46 (.branch 43 (.branch 41 (.leaf (-26)) (.branch 42 (.leaf (-25)) (.leaf (-24)))) (.branch 44 (.leaf (-23)) (.branch 45 (.leaf (-22)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18)))) (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))))) (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 61 (.branch 58 (.branch 57 (.leaf (-10)) (.leaf (-9))) (.branch 59 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6))))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_290_4941 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (8))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (7)) (.leaf (5))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (6))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (8)) (.leaf (1)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (5))) (.branch 36 (.leaf (2)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (6))) (.branch 40 (.leaf (3)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (7))) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (2))) (.branch 48 (.leaf (5)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (1)) (.leaf (3))) (.branch 52 (.leaf (0)) (.leaf (6)))) (.branch 55 (.branch 54 (.leaf (8)) (.leaf (1))) (.branch 56 (.leaf (0)) (.leaf (4))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (2)) (.leaf (1))) (.branch 60 (.leaf (0)) (.leaf (5)))) (.branch 63 (.branch 62 (.leaf (3)) (.leaf (0))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (7)) (.leaf (6)))))))))
  code := certificateP9_4941
  counts := ![(.branch 30 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 33 (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 50 (.branch 42 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 59 (.branch 55 (.leaf (12)) (.leaf (13))) (.branch 64 (.leaf (14)) (.leaf (15)))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 61 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 53 (.leaf (3)) (.branch 66 (.leaf (4)) (.leaf (5))))),
  (.branch 43 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-12)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-46)) (.leaf (-47)))),
  (.branch 35 (.branch 9 (.leaf (0)) (.branch 22 (.leaf (-21)) (.leaf (-22)))) (.branch 48 (.leaf (-23)) (.branch 61 (.leaf (-24)) (.leaf (-25))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (-1))) (.branch 39 (.leaf (-2)) (.leaf (-3)))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 60 (.branch 51 (.leaf (-14)) (.leaf (-13))) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 61 (.branch 58 (.branch 18 (.leaf (-47)) (.leaf (-45))) (.branch 59 (.leaf (-40)) (.branch 60 (.leaf (-35)) (.leaf (-30))))) (.branch 63 (.branch 62 (.leaf (-25)) (.leaf (-20))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 63 (.branch 62 (.leaf (-25)) (.leaf (-20))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 40 (.leaf (-3)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_290_4942 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (4)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (2))) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (8)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (5)) (.leaf (2)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (4)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (6))) (.branch 40 (.leaf (2)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (5))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (2))) (.branch 48 (.leaf (4)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (7)) (.leaf (3))) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (5)) (.leaf (2))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (0)) (.leaf (8)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (5)) (.leaf (3)))))))))
  code := certificateP9_4942
  counts := ![(.branch 31 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 30 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 44 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 66 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 61 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-27))),
  (.branch 17 (.leaf (0)) (.leaf (-16))),
  (.branch 28 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 61 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 64 (.branch 58 (.leaf (-7)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 63 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 59 (.leaf (-2)) (.leaf (0))),
  (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 52 (.branch 45 (.branch 42 (.branch 40 (.leaf (-27)) (.branch 41 (.leaf (-26)) (.leaf (-25)))) (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19)))) (.branch 50 (.branch 49 (.leaf (-18)) (.leaf (-17))) (.branch 51 (.leaf (-16)) (.leaf (-15)))))) (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_290_4943 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (2)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (3)) (.leaf (7)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (8)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (5)) (.leaf (2)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (4)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (6))) (.branch 40 (.leaf (2)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (5))) (.branch 44 (.leaf (3)) (.leaf (4)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (7)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (3)) (.leaf (4)))) (.branch 55 (.branch 54 (.leaf (5)) (.leaf (0))) (.branch 56 (.leaf (2)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (3)) (.leaf (0))) (.branch 60 (.leaf (8)) (.leaf (4)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (5)) (.leaf (3)))))))))
  code := certificateP9_4943
  counts := ![(.branch 31 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 55 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 59 (.leaf (14)) (.branch 64 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 44 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 66 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.branch 60 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.branch 13 (.leaf (-12)) (.leaf (-13))))) (.branch 42 (.branch 34 (.leaf (-14)) (.branch 38 (.leaf (-15)) (.leaf (-16)))) (.branch 46 (.leaf (-17)) (.branch 50 (.leaf (-18)) (.leaf (-19)))))),
  (.branch 18 (.branch 2 (.leaf (0)) (.leaf (-18))) (.branch 51 (.leaf (-22)) (.leaf (-25)))),
  (.branch 25 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 62 (.leaf (-10)) (.leaf (-11)))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 36 (.leaf (-2)) (.branch 58 (.leaf (-3)) (.leaf (-4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-17))) (.branch 20 (.leaf (-18)) (.branch 28 (.leaf (-19)) (.leaf (-20))))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-27))),
  (.branch 16 (.leaf (0)) (.leaf (-17))),
  (.branch 27 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 60 (.branch 51 (.leaf (-19)) (.leaf (-18))) (.branch 65 (.leaf (-16)) (.leaf (-13)))),
  (.branch 58 (.branch 52 (.leaf (-25)) (.leaf (-23))) (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-16)) (.leaf (-11))))),
  (.branch 64 (.branch 63 (.leaf (-11)) (.leaf (-9))) (.branch 65 (.leaf (-7)) (.leaf (-5)))),
  (.branch 59 (.leaf (-4)) (.branch 60 (.leaf (-2)) (.leaf (0)))),
  (.branch 63 (.branch 62 (.leaf (-20)) (.leaf (-16))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-1)),
  (.branch 52 (.branch 45 (.branch 42 (.branch 40 (.leaf (-27)) (.branch 41 (.leaf (-26)) (.leaf (-25)))) (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19)))) (.branch 50 (.branch 49 (.leaf (-18)) (.leaf (-17))) (.branch 51 (.leaf (-16)) (.leaf (-15)))))) (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))) (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.leaf (-10))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_290_4944 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (8))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (6)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (2))) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (5))) (.branch 27 (.leaf (0)) (.leaf (8)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (6)) (.leaf (2)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (4)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (7))) (.branch 40 (.leaf (2)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (5))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (2))) (.branch 48 (.leaf (6)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (8)) (.leaf (3))) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (4)) (.leaf (2))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (3)) (.leaf (5))) (.branch 60 (.leaf (0)) (.leaf (7)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (6)) (.leaf (3)))))))))
  code := certificateP9_4944
  counts := ![(.branch 31 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 30 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 44 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 66 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4))))),
  (.branch 39 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-25))),
  (.branch 10 (.leaf (0)) (.branch 26 (.leaf (-13)) (.leaf (-14)))),
  (.branch 15 (.leaf (0)) (.leaf (-3))),
  (.branch 17 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 61 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 64 (.branch 58 (.leaf (-7)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 63 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 59 (.leaf (-2)) (.leaf (0))),
  (.branch 59 (.branch 56 (.branch 38 (.leaf (-25)) (.branch 55 (.leaf (-24)) (.leaf (-22)))) (.branch 57 (.leaf (-20)) (.branch 58 (.leaf (-18)) (.leaf (-16))))) (.branch 62 (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 62 (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.leaf (-3)) (.leaf (-2))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_290_4945 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (7))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (6))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (3))) (.branch 15 (.leaf (1)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (0))) (.branch 19 (.leaf (2)) (.leaf (7)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (6))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (8))) (.branch 27 (.leaf (2)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (7)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (6)))) (.branch 39 (.branch 38 (.leaf (3)) (.leaf (8))) (.branch 40 (.leaf (0)) (.leaf (4))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (5))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (7)) (.leaf (3))) (.branch 48 (.leaf (1)) (.leaf (4)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (6)) (.leaf (0))) (.branch 52 (.leaf (2)) (.leaf (8)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (3))) (.branch 56 (.leaf (0)) (.leaf (5))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (4)) (.leaf (7))) (.branch 60 (.leaf (2)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (3))) (.branch 64 (.leaf (6)) (.branch 65 (.leaf (8)) (.leaf (4)))))))))
  code := certificateP9_4945
  counts := ![(.branch 29 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 53 (.leaf (3)) (.branch 65 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-14))) (.branch 21 (.leaf (-15)) (.branch 54 (.leaf (-17)) (.leaf (-18))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 19 (.leaf (-22)) (.branch 27 (.leaf (-23)) (.leaf (-24))))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (-37))) (.branch 43 (.leaf (-38)) (.leaf (-40)))),
  (.branch 10 (.leaf (0)) (.leaf (-13))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (-29)) (.leaf (-31)))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (-1))) (.branch 39 (.leaf (-2)) (.branch 65 (.leaf (-3)) (.leaf (-5)))))]
  high := ![(.branch 63 (.branch 57 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 63 (.branch 55 (.leaf (-18)) (.branch 62 (.leaf (-17)) (.leaf (-14)))) (.branch 64 (.leaf (-11)) (.branch 65 (.leaf (-8)) (.leaf (-5))))),
  (.branch 63 (.branch 61 (.leaf (-24)) (.branch 62 (.leaf (-20)) (.leaf (-16)))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 64 (.branch 39 (.leaf (-13)) (.leaf (-12))) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.branch 50 (.leaf (-2)) (.leaf (0))),
  (.branch 61 (.branch 58 (.branch 44 (.leaf (-40)) (.leaf (-37))) (.branch 59 (.leaf (-33)) (.branch 60 (.leaf (-29)) (.leaf (-25))))) (.branch 63 (.branch 62 (.leaf (-21)) (.leaf (-17))) (.branch 64 (.leaf (-13)) (.branch 65 (.leaf (-9)) (.leaf (-5)))))),
  (.branch 51 (.branch 11 (.leaf (-13)) (.leaf (-12))) (.branch 65 (.leaf (-9)) (.leaf (-5)))),
  (.branch 62 (.branch 60 (.branch 33 (.leaf (-31)) (.leaf (-29))) (.branch 61 (.leaf (-25)) (.leaf (-21)))) (.branch 64 (.branch 63 (.leaf (-17)) (.leaf (-13))) (.branch 65 (.leaf (-9)) (.leaf (-5))))),
  (.leaf (-5))]
def witnessP9_290_4946 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (6))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (5))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (8)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (2)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (3)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (6))) (.branch 40 (.leaf (1)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (4)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (5))) (.branch 48 (.leaf (0)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (7)) (.leaf (0))) (.branch 52 (.leaf (1)) (.leaf (3)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (2))) (.branch 56 (.leaf (1)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (4)) (.leaf (1))) (.branch 60 (.leaf (0)) (.leaf (8)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (0))) (.branch 64 (.leaf (5)) (.branch 65 (.leaf (1)) (.leaf (2)))))))))
  code := certificateP9_4946
  counts := ![(.branch 32 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))) (.branch 48 (.branch 38 (.branch 35 (.leaf (11)) (.leaf (12))) (.branch 41 (.leaf (13)) (.branch 45 (.leaf (14)) (.leaf (15))))) (.branch 57 (.branch 51 (.leaf (16)) (.branch 54 (.leaf (17)) (.leaf (18)))) (.branch 60 (.leaf (19)) (.branch 63 (.leaf (20)) (.leaf (21))))))),
  (.branch 34 (.branch 15 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))) (.branch 49 (.branch 40 (.branch 37 (.leaf (11)) (.leaf (12))) (.branch 43 (.leaf (13)) (.branch 46 (.leaf (14)) (.leaf (15))))) (.branch 59 (.branch 52 (.leaf (16)) (.branch 56 (.leaf (17)) (.leaf (18)))) (.branch 62 (.leaf (19)) (.branch 65 (.leaf (20)) (.leaf (21))))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 61 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 16 (.branch 13 (.leaf (-18)) (.leaf (-19))) (.branch 19 (.leaf (-20)) (.leaf (-21))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-27))),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-27))),
  (.branch 17 (.leaf (0)) (.leaf (-16))),
  (.branch 28 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-14)) (.leaf (-7)))),
  (.branch 53 (.leaf (-10)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 59 (.branch 55 (.branch 37 (.leaf (-27)) (.branch 54 (.leaf (-26)) (.leaf (-24)))) (.branch 57 (.branch 56 (.leaf (-22)) (.leaf (-20))) (.branch 58 (.leaf (-18)) (.leaf (-16))))) (.branch 62 (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-16)) (.leaf (-14))) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 48 (.leaf (-5)) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 45 (.branch 42 (.branch 40 (.leaf (-27)) (.branch 41 (.leaf (-26)) (.leaf (-25)))) (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19)))) (.branch 50 (.branch 49 (.leaf (-18)) (.leaf (-17))) (.branch 51 (.leaf (-16)) (.leaf (-15)))))) (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_290_4947 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (0))) (.branch 15 (.leaf (3)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (0))) (.branch 19 (.leaf (4)) (.leaf (8)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (2)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (7)) (.branch 32 (.leaf (2)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (5)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (2))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (8)) (.leaf (0))) (.branch 44 (.leaf (1)) (.leaf (6)))) (.branch 47 (.branch 46 (.leaf (4)) (.leaf (0))) (.branch 48 (.leaf (3)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (5)) (.leaf (7)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (0))) (.branch 56 (.leaf (2)) (.leaf (3))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (1)) (.leaf (0))) (.branch 60 (.leaf (4)) (.leaf (6)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (0))) (.branch 64 (.leaf (8)) (.branch 65 (.leaf (2)) (.leaf (5)))))))))
  code := certificateP9_4947
  counts := ![(.branch 30 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 47 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.branch 43 (.leaf (12)) (.leaf (13))))) (.branch 55 (.branch 51 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 29 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 39 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 32 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 66 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-17)) (.leaf (-22)))) (.branch 40 (.branch 10 (.leaf (-27)) (.leaf (-32))) (.branch 43 (.leaf (-36)) (.leaf (-41))))),
  (.branch 25 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))) (.branch 58 (.branch 29 (.leaf (-5)) (.leaf (-6))) (.branch 62 (.leaf (-7)) (.leaf (-8))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (-2))) (.branch 56 (.leaf (-9)) (.leaf (-14)))),
  (.branch 24 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 57 (.leaf (-21)) (.leaf (-24)))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.branch 38 (.leaf (-1)) (.leaf (-5)))),
  (.branch 12 (.leaf (0)) (.branch 28 (.leaf (-9)) (.leaf (-10)))),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 20 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 56 (.branch 48 (.branch 44 (.leaf (-41)) (.leaf (-40))) (.branch 52 (.leaf (-39)) (.leaf (-38)))) (.branch 64 (.branch 60 (.leaf (-37)) (.leaf (-36))) (.branch 65 (.leaf (-30)) (.leaf (-24))))),
  (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-5)))),
  (.branch 57 (.leaf (-14)) (.leaf (-13))),
  (.branch 61 (.branch 59 (.branch 58 (.leaf (-24)) (.leaf (-22))) (.branch 60 (.leaf (-20)) (.leaf (-18)))) (.branch 63 (.branch 62 (.leaf (-16)) (.leaf (-14))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-10)) (.leaf (-8)))))),
  (.branch 62 (.branch 47 (.branch 6 (.leaf (-17)) (.leaf (-16))) (.branch 61 (.leaf (-15)) (.leaf (-13)))) (.branch 64 (.branch 63 (.leaf (-11)) (.leaf (-9))) (.branch 65 (.leaf (-7)) (.leaf (-5))))),
  (.branch 53 (.branch 39 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-2)) (.leaf (0)))),
  (.branch 63 (.branch 62 (.leaf (-10)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 65 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_290_4948 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (8)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (1)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (7)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (4))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (6)) (.leaf (2)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (8)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (5))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (4)) (.leaf (0))) (.branch 44 (.leaf (2)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (3))) (.branch 48 (.leaf (0)) (.leaf (6)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (7)) (.leaf (1))) (.branch 52 (.leaf (0)) (.leaf (4)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (2))) (.branch 56 (.leaf (1)) (.leaf (5))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (3))) (.branch 60 (.leaf (0)) (.leaf (8)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (4))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (6)) (.leaf (2)))))))))
  code := certificateP9_4948
  counts := ![(.branch 31 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))) (.branch 48 (.branch 40 (.branch 34 (.leaf (11)) (.branch 37 (.leaf (12)) (.leaf (13)))) (.branch 43 (.leaf (14)) (.branch 46 (.leaf (15)) (.leaf (16))))) (.branch 58 (.branch 52 (.leaf (17)) (.branch 54 (.leaf (18)) (.leaf (19)))) (.branch 60 (.leaf (20)) (.branch 64 (.leaf (21)) (.leaf (22))))))),
  (.branch 29 (.branch 12 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-18))) (.branch 39 (.leaf (-26)) (.leaf (-29)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (-17)) (.leaf (-18)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 17 (.leaf (0)) (.branch 38 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 61 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 63 (.branch 40 (.leaf (-29)) (.branch 57 (.leaf (-28)) (.leaf (-26)))) (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-16)) (.leaf (-11))))),
  (.leaf (0)),
  (.branch 62 (.branch 60 (.branch 48 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 61 (.branch 59 (.branch 58 (.leaf (-18)) (.leaf (-16))) (.branch 60 (.leaf (-14)) (.leaf (-12)))) (.branch 63 (.branch 62 (.leaf (-10)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (-2)),
  (.branch 57 (.branch 53 (.branch 51 (.branch 6 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))) (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.leaf (-10))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.branch 39 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_290_4949 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (5)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (6))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (4))) (.branch 40 (.leaf (1)) (.leaf (2))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (3))) (.branch 44 (.leaf (7)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (0)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (5))) (.branch 56 (.leaf (0)) (.leaf (3))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (1)) (.leaf (2))) (.branch 60 (.leaf (0)) (.leaf (4)))) (.branch 63 (.branch 62 (.leaf (3)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (2)) (.leaf (8)))))))))
  code := certificateP9_4949
  counts := ![(.branch 31 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 30 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 32 (.branch 14 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 37 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 36 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1))),
  (.branch 66 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 48 (.leaf (-15)) (.leaf (-18)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 25 (.leaf (-12)) (.branch 58 (.leaf (-14)) (.leaf (-15))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 41 (.leaf (-14)) (.leaf (-20)))),
  (.branch 29 (.branch 3 (.leaf (0)) (.leaf (-15))) (.branch 62 (.leaf (-19)) (.leaf (-22)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.branch 22 (.leaf (0)) (.leaf (-44))),
  (.branch 44 (.leaf (0)) (.leaf (-22))),
  (.leaf (0))]
  high := ![(.branch 57 (.branch 49 (.leaf (-18)) (.branch 53 (.leaf (-17)) (.leaf (-16)))) (.branch 61 (.leaf (-15)) (.branch 65 (.leaf (-14)) (.leaf (-10))))),
  (.branch 64 (.branch 59 (.leaf (-15)) (.leaf (-14))) (.branch 65 (.leaf (-10)) (.leaf (-6)))),
  (.branch 48 (.branch 42 (.leaf (-20)) (.leaf (-19))) (.branch 54 (.leaf (-18)) (.branch 60 (.leaf (-17)) (.leaf (-16))))),
  (.branch 64 (.branch 63 (.leaf (-22)) (.leaf (-18))) (.branch 65 (.leaf (-14)) (.leaf (-10)))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 44 (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (-44)) (.leaf (-43))) (.branch 25 (.leaf (-42)) (.branch 26 (.leaf (-41)) (.leaf (-40))))) (.branch 30 (.branch 28 (.leaf (-39)) (.branch 29 (.leaf (-38)) (.leaf (-37)))) (.branch 31 (.leaf (-36)) (.branch 32 (.leaf (-35)) (.leaf (-34)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (-33)) (.leaf (-32))) (.branch 36 (.leaf (-31)) (.branch 37 (.leaf (-30)) (.leaf (-29))))) (.branch 41 (.branch 39 (.leaf (-28)) (.branch 40 (.leaf (-27)) (.leaf (-26)))) (.branch 42 (.leaf (-25)) (.branch 43 (.leaf (-24)) (.leaf (-23))))))) (.branch 55 (.branch 49 (.branch 46 (.branch 45 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18))))) (.branch 52 (.branch 50 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 55 (.branch 49 (.branch 46 (.branch 45 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18))))) (.branch 52 (.branch 50 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_290_4950 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (7))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (3))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (8)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (6))) (.branch 27 (.leaf (0)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (7)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (4))) (.branch 40 (.leaf (6)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (8))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (5)) (.leaf (3))) (.branch 48 (.leaf (1)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (4)) (.leaf (2))) (.branch 52 (.leaf (0)) (.leaf (6)))) (.branch 55 (.branch 54 (.leaf (7)) (.leaf (1))) (.branch 56 (.leaf (0)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (3)) (.leaf (5))) (.branch 60 (.leaf (0)) (.leaf (4)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (0))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (8)) (.leaf (6)))))))))
  code := certificateP9_4950
  counts := ![(.branch 30 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 40 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 53 (.leaf (3)) (.branch 66 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 43 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-23)) (.leaf (-24)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 33 (.branch 7 (.leaf (0)) (.branch 20 (.leaf (-31)) (.leaf (-32)))) (.branch 46 (.leaf (-33)) (.branch 59 (.leaf (-34)) (.leaf (-35))))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2)))),
  (.branch 10 (.leaf (0)) (.leaf (-12))),
  (.branch 21 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 63 (.branch 49 (.leaf (-24)) (.branch 56 (.leaf (-22)) (.leaf (-20)))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 58 (.branch 38 (.leaf (-13)) (.leaf (-12))) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 62 (.branch 60 (.leaf (-35)) (.branch 61 (.leaf (-30)) (.leaf (-25)))) (.branch 64 (.branch 63 (.leaf (-20)) (.leaf (-15))) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 27 (.leaf (-2)) (.leaf (0))),
  (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_290_4951 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (6))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (3))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (7)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (8)) (.leaf (1)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (3)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (4))) (.branch 40 (.leaf (2)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (6))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (3))) (.branch 48 (.leaf (2)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (1))) (.branch 52 (.leaf (0)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (7)) (.leaf (1))) (.branch 56 (.leaf (0)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (3)) (.leaf (1))) (.branch 60 (.leaf (0)) (.leaf (4)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (0))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (8)) (.leaf (2)))))))))
  code := certificateP9_4951
  counts := ![(.branch 30 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 33 (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 51 (.branch 42 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 59 (.branch 55 (.leaf (12)) (.leaf (13))) (.branch 64 (.leaf (14)) (.leaf (15)))))),
  (.branch 35 (.branch 18 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))) (.branch 53 (.branch 44 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 48 (.leaf (10)) (.leaf (11)))) (.branch 62 (.branch 57 (.leaf (12)) (.leaf (13))) (.branch 66 (.leaf (14)) (.leaf (15)))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 39 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2)))),
  (.branch 32 (.leaf (0)) (.branch 65 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-12)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 17 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 10 (.leaf (0)) (.leaf (-23))),
  (.branch 21 (.leaf (0)) (.leaf (-12))),
  (.branch 32 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 60 (.leaf (-13)) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.branch 49 (.leaf (-2)) (.branch 58 (.leaf (-1)) (.leaf (0)))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.branch 48 (.branch 45 (.branch 44 (.leaf (-23)) (.leaf (-22))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19))))) (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_290_4952 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (8))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (6)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (8))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (5))) (.branch 27 (.leaf (3)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (4)) (.leaf (7)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (8))) (.branch 40 (.leaf (5)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (0))) (.branch 44 (.leaf (6)) (.leaf (3)))) (.branch 47 (.branch 46 (.leaf (4)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (7)) (.leaf (3))) (.branch 52 (.leaf (0)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (5)) (.leaf (8))) (.branch 56 (.leaf (2)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (1)) (.leaf (4))) (.branch 60 (.leaf (3)) (.leaf (6)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (2))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (5)) (.leaf (7)))))))))
  code := certificateP9_4952
  counts := ![(.branch 29 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 48 (.branch 38 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 43 (.leaf (9)) (.leaf (10)))) (.branch 57 (.branch 52 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 37 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 40 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 54 (.leaf (3)) (.branch 65 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-26))) (.branch 19 (.leaf (-31)) (.leaf (-32)))),
  (.branch 2 (.leaf (0)) (.branch 35 (.leaf (-11)) (.leaf (-14)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 42 (.leaf (-18)) (.leaf (-21)))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 51 (.leaf (-24)) (.leaf (-29)))),
  (.branch 7 (.leaf (0)) (.branch 32 (.leaf (-13)) (.leaf (-17)))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (-1))) (.branch 65 (.leaf (-2)) (.leaf (-5)))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (-21)) (.leaf (-22))))]
  high := ![(.branch 63 (.branch 53 (.leaf (-32)) (.branch 58 (.leaf (-30)) (.leaf (-28)))) (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-14)) (.leaf (-7))))),
  (.branch 59 (.branch 36 (.leaf (-14)) (.leaf (-13))) (.branch 65 (.leaf (-12)) (.leaf (-9)))),
  (.branch 57 (.branch 43 (.leaf (-21)) (.branch 50 (.leaf (-20)) (.leaf (-19)))) (.branch 64 (.leaf (-18)) (.branch 65 (.leaf (-14)) (.leaf (-10))))),
  (.branch 62 (.branch 52 (.leaf (-29)) (.branch 61 (.leaf (-28)) (.leaf (-25)))) (.branch 64 (.branch 63 (.leaf (-22)) (.leaf (-19))) (.branch 65 (.leaf (-16)) (.leaf (-13))))),
  (.branch 62 (.branch 60 (.leaf (-17)) (.branch 61 (.leaf (-15)) (.leaf (-13)))) (.branch 64 (.branch 63 (.leaf (-11)) (.leaf (-9))) (.branch 65 (.leaf (-7)) (.leaf (-5))))),
  (.leaf (-5)),
  (.branch 63 (.branch 45 (.leaf (-11)) (.branch 62 (.leaf (-10)) (.leaf (-8)))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-22)) (.leaf (-20))) (.branch 58 (.leaf (-18)) (.branch 59 (.leaf (-16)) (.leaf (-14))))) (.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-10)) (.leaf (-8)))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))))]
def witnessP9_290_4953 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (3)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (8))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (5)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (3)) (.leaf (6)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (4)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (5)) (.leaf (0))) (.branch 40 (.leaf (3)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (4)) (.leaf (0))) (.branch 44 (.leaf (2)) (.leaf (7)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (5)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (4)) (.leaf (2))) (.branch 52 (.leaf (0)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (8))) (.branch 56 (.leaf (2)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (4)) (.leaf (1))) (.branch 60 (.leaf (5)) (.leaf (3)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (2))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (4)) (.leaf (6)))))))))
  code := certificateP9_4953
  counts := ![(.branch 29 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 48 (.branch 39 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 43 (.leaf (9)) (.leaf (10)))) (.branch 57 (.branch 52 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 54 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.leaf (0)) (.branch 66 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 19 (.leaf (-17)) (.branch 52 (.leaf (-19)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 35 (.leaf (-15)) (.leaf (-21)))),
  (.branch 23 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 56 (.leaf (-16)) (.leaf (-19)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 46 (.leaf (-12)) (.leaf (-13)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 42 (.leaf (-4)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-21))),
  (.branch 22 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 63 (.branch 53 (.leaf (-20)) (.branch 58 (.leaf (-19)) (.leaf (-18)))) (.branch 64 (.leaf (-14)) (.branch 65 (.leaf (-10)) (.leaf (-6))))),
  (.branch 36 (.leaf (-21)) (.branch 65 (.leaf (-20)) (.leaf (-16)))),
  (.branch 64 (.branch 57 (.leaf (-19)) (.leaf (-18))) (.branch 65 (.leaf (-14)) (.leaf (-10)))),
  (.branch 63 (.branch 62 (.leaf (-13)) (.leaf (-11))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-7)) (.leaf (-5))))),
  (.branch 43 (.leaf (-6)) (.leaf (-5))),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 55 (.branch 50 (.branch 47 (.branch 46 (.leaf (-21)) (.leaf (-20))) (.branch 48 (.leaf (-19)) (.branch 49 (.leaf (-18)) (.leaf (-17))))) (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_290_4954 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (5))) (.branch 15 (.leaf (1)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (3))) (.branch 19 (.leaf (7)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (8))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (1)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (5)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (3)) (.leaf (6))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (3))) (.branch 48 (.leaf (4)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (1))) (.branch 52 (.leaf (7)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (5)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (3)) (.leaf (8))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (0)) (.leaf (2)))))))))
  code := certificateP9_4954
  counts := ![(.branch 31 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 61 (.leaf (16)) (.branch 65 (.leaf (17)) (.leaf (18))))))),
  (.branch 33 (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 51 (.branch 42 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 59 (.branch 55 (.leaf (12)) (.leaf (13))) (.branch 64 (.leaf (14)) (.leaf (15)))))),
  (.branch 34 (.branch 16 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 54 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.branch 63 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 23 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 45 (.leaf (-18)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-12)) (.leaf (-13)))),
  (.branch 38 (.branch 16 (.leaf (0)) (.leaf (-3))) (.branch 60 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.leaf (-18))),
  (.branch 14 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-25))),
  (.branch 19 (.leaf (0)) (.leaf (-14))),
  (.branch 30 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 54 (.branch 46 (.leaf (-22)) (.branch 50 (.leaf (-21)) (.leaf (-20)))) (.branch 58 (.leaf (-19)) (.branch 62 (.leaf (-18)) (.leaf (-17))))),
  (.branch 60 (.leaf (-13)) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.branch 61 (.leaf (-7)) (.leaf (-4))) (.branch 63 (.leaf (-1)) (.leaf (0)))),
  (.branch 63 (.branch 55 (.leaf (-14)) (.leaf (-12))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.branch 52 (.branch 50 (.branch 49 (.leaf (-18)) (.leaf (-17))) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 54 (.branch 53 (.leaf (-14)) (.leaf (-13))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 47 (.branch 44 (.branch 42 (.leaf (-25)) (.branch 43 (.leaf (-24)) (.leaf (-23)))) (.branch 45 (.leaf (-22)) (.branch 46 (.leaf (-21)) (.leaf (-20))))) (.branch 50 (.branch 48 (.leaf (-19)) (.branch 49 (.leaf (-18)) (.leaf (-17)))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-15)) (.leaf (-14)))))) (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_290_4955 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (4)) (.leaf (8))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (7)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (3)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (0))) (.branch 23 (.leaf (4)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (8)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (0))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (4)) (.leaf (7)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (3)) (.leaf (6)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (4)) (.leaf (8))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (0))) (.branch 44 (.leaf (3)) (.leaf (5)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (4)) (.leaf (7)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (3)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (6)) (.leaf (0))) (.branch 56 (.leaf (4)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (8)) (.leaf (0))) (.branch 60 (.leaf (3)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (5)) (.leaf (0))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (4)) (.leaf (7)))))))))
  code := certificateP9_4955
  counts := ![(.branch 30 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 55 (.branch 51 (.leaf (12)) (.leaf (13))) (.branch 59 (.leaf (14)) (.branch 63 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-25)) (.leaf (-26)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-16)) (.leaf (-17)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 20 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 19 (.leaf (-22)) (.branch 27 (.leaf (-23)) (.leaf (-24))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 23 (.leaf (-6)) (.leaf (-7)))),
  (.branch 12 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-25))),
  (.branch 16 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 64 (.branch 39 (.leaf (-26)) (.leaf (-24))) (.branch 65 (.leaf (-16)) (.leaf (-8)))),
  (.branch 63 (.branch 54 (.leaf (-17)) (.branch 62 (.leaf (-15)) (.leaf (-12)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 65 (.leaf (-6)) (.leaf (-3))),
  (.branch 63 (.branch 61 (.leaf (-24)) (.branch 62 (.leaf (-20)) (.leaf (-16)))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 57 (.leaf (-7)) (.leaf (-4))),
  (.branch 63 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 59 (.branch 56 (.branch 38 (.leaf (-25)) (.branch 55 (.leaf (-24)) (.leaf (-22)))) (.branch 57 (.leaf (-20)) (.branch 58 (.leaf (-18)) (.leaf (-16))))) (.branch 62 (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 50 (.leaf (-1)) (.leaf (0))),
  (.branch 61 (.branch 59 (.branch 42 (.leaf (-17)) (.leaf (-16))) (.branch 60 (.leaf (-14)) (.leaf (-12)))) (.branch 63 (.branch 62 (.leaf (-10)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))))]
def witnessP9_290_4956 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (8))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (4))) (.branch 15 (.leaf (6)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (3)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (7)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (3)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (8)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (3)) (.leaf (6)))) (.branch 39 (.branch 38 (.leaf (4)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (5))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (7))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (4))) (.branch 48 (.leaf (6)) (.leaf (5)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (3)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (8)) (.leaf (4))) (.branch 56 (.leaf (0)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (5)) (.leaf (6))) (.branch 60 (.leaf (3)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (4))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (7)) (.leaf (5)))))))))
  code := certificateP9_4956
  counts := ![(.branch 29 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 43 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-16)) (.leaf (-17)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 20 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 19 (.leaf (-22)) (.branch 27 (.leaf (-23)) (.leaf (-24))))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 63 (.branch 57 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 63 (.branch 54 (.leaf (-17)) (.branch 62 (.leaf (-15)) (.leaf (-12)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 65 (.leaf (-6)) (.leaf (-3))),
  (.branch 63 (.branch 61 (.leaf (-24)) (.branch 62 (.leaf (-20)) (.leaf (-16)))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 64 (.branch 39 (.leaf (-13)) (.leaf (-12))) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.branch 50 (.leaf (-2)) (.leaf (0))),
  (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_290_4957 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (5))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (7)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (1)) (.leaf (2)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (4)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (2)) (.leaf (1))) (.branch 40 (.leaf (3)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (6)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (5))) (.branch 48 (.leaf (0)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (1)) (.leaf (3))) (.branch 52 (.leaf (0)) (.leaf (4)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (2))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (8)) (.leaf (0))) (.branch 60 (.leaf (2)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (3)) (.leaf (0))) (.branch 64 (.leaf (5)) (.branch 65 (.leaf (1)) (.leaf (2)))))))))
  code := certificateP9_4957
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 32 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 50 (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 54 (.leaf (14)) (.leaf (15))) (.branch 61 (.leaf (16)) (.branch 65 (.leaf (17)) (.leaf (18))))))),
  (.branch 33 (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 58 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-27))),
  (.branch 14 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-24))),
  (.branch 25 (.leaf (0)) (.leaf (-41))),
  (.branch 58 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 64 (.branch 60 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 58 (.leaf (-5)) (.branch 62 (.leaf (-4)) (.leaf (-3)))),
  (.branch 61 (.leaf (-1)) (.leaf (0))),
  (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 59 (.branch 55 (.branch 37 (.leaf (-27)) (.branch 54 (.leaf (-26)) (.leaf (-24)))) (.branch 57 (.branch 56 (.leaf (-22)) (.leaf (-20))) (.branch 58 (.leaf (-18)) (.leaf (-16))))) (.branch 62 (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 48 (.leaf (-5)) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 54 (.branch 48 (.branch 45 (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22)))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19))))) (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 35 (.branch 30 (.branch 27 (.branch 26 (.leaf (-41)) (.leaf (-40))) (.branch 28 (.leaf (-39)) (.branch 29 (.leaf (-38)) (.leaf (-37))))) (.branch 32 (.branch 31 (.leaf (-36)) (.leaf (-35))) (.branch 33 (.leaf (-34)) (.branch 34 (.leaf (-33)) (.leaf (-32)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-31)) (.leaf (-30))) (.branch 38 (.leaf (-29)) (.branch 39 (.leaf (-28)) (.leaf (-27))))) (.branch 42 (.branch 41 (.leaf (-26)) (.leaf (-25))) (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22))))))) (.branch 55 (.branch 50 (.branch 47 (.branch 46 (.leaf (-21)) (.leaf (-20))) (.branch 48 (.leaf (-19)) (.branch 49 (.leaf (-18)) (.leaf (-17))))) (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_290_4958 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (7))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (6)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (8)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (7)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (2)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (4)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (8))) (.branch 40 (.leaf (1)) (.leaf (2))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (5))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (6))) (.branch 48 (.leaf (0)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (7)) (.leaf (0))) (.branch 52 (.leaf (1)) (.leaf (4)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (3))) (.branch 56 (.leaf (2)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (5))) (.branch 60 (.leaf (0)) (.leaf (8)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (2))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (6)) (.leaf (3)))))))))
  code := certificateP9_4958
  counts := ![(.branch 32 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 16 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))) (.branch 48 (.branch 38 (.branch 36 (.leaf (11)) (.leaf (12))) (.branch 42 (.leaf (13)) (.branch 45 (.leaf (14)) (.leaf (15))))) (.branch 58 (.branch 51 (.leaf (16)) (.branch 54 (.leaf (17)) (.leaf (18)))) (.branch 60 (.leaf (19)) (.branch 64 (.leaf (20)) (.leaf (21))))))),
  (.branch 30 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 41 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 63 (.leaf (8)) (.leaf (9)))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 7 (.leaf (-14)) (.leaf (-15)))) (.branch 38 (.branch 16 (.leaf (-16)) (.leaf (-18))) (.branch 60 (.leaf (-19)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-8)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 19 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 53 (.leaf (-14)) (.leaf (-15)))),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (-8)) (.leaf (-9)))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (-2))) (.branch 47 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 61 (.leaf (-20)) (.branch 65 (.leaf (-15)) (.leaf (-9)))),
  (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 59 (.branch 56 (.branch 54 (.leaf (-15)) (.branch 55 (.leaf (-14)) (.leaf (-13)))) (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-11)) (.leaf (-10))))) (.branch 62 (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7)))) (.branch 64 (.branch 63 (.leaf (-6)) (.leaf (-5))) (.branch 65 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 62 (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7)))) (.branch 64 (.branch 63 (.leaf (-6)) (.leaf (-5))) (.branch 65 (.leaf (-4)) (.leaf (-3))))),
  (.branch 48 (.leaf (-4)) (.leaf (-3))),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_290_4959 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (8)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (6))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (7))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (2))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (8)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (4)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (6)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (2))) (.branch 44 (.leaf (7)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (1)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (5))) (.branch 52 (.leaf (3)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (8))) (.branch 56 (.leaf (0)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (4)) (.leaf (3))) (.branch 60 (.leaf (0)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (6)) (.leaf (2))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (3)) (.leaf (7)))))))))
  code := certificateP9_4959
  counts := ![(.branch 31 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 28 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 37 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 39 (.leaf (5)) (.branch 46 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 65 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-23))) (.branch 21 (.leaf (-26)) (.leaf (-27)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-16)))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (-3))) (.branch 32 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 18 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 61 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 63 (.branch 55 (.leaf (-27)) (.branch 62 (.leaf (-25)) (.leaf (-20)))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 64 (.branch 44 (.leaf (-16)) (.leaf (-15))) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (-5)),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 54 (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_290_4960 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (3)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (4))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (5))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (2))) (.branch 19 (.leaf (8)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (6))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (4)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (5)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (4))) (.branch 40 (.leaf (3)) (.leaf (7))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (5))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (1)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (2))) (.branch 52 (.leaf (8)) (.leaf (3)))) (.branch 55 (.branch 54 (.leaf (4)) (.leaf (1))) (.branch 56 (.leaf (0)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (5)) (.leaf (3))) (.branch 60 (.leaf (0)) (.leaf (4)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (6))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (5)) (.leaf (3)))))))))
  code := certificateP9_4960
  counts := ![(.branch 27 (.branch 12 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 40 (.leaf (5)) (.branch 46 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 54 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 30 (.leaf (0)) (.branch 63 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 27 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 16 (.leaf (-7)) (.leaf (-8)))) (.branch 49 (.branch 38 (.leaf (-9)) (.leaf (-10))) (.branch 60 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-23)) (.leaf (-24)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 17 (.leaf (-14)) (.leaf (-15)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 30 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-25))),
  (.branch 19 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-11)) (.leaf (-10)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7))))),
  (.branch 63 (.branch 49 (.leaf (-24)) (.branch 56 (.leaf (-22)) (.leaf (-20)))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 58 (.branch 38 (.leaf (-13)) (.leaf (-12))) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.branch 60 (.leaf (-2)) (.leaf (0))),
  (.branch 63 (.branch 62 (.leaf (-15)) (.leaf (-12))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 51 (.leaf (-4)) (.leaf (-3))),
  (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 53 (.branch 47 (.branch 44 (.branch 42 (.leaf (-25)) (.branch 43 (.leaf (-24)) (.leaf (-23)))) (.branch 45 (.leaf (-22)) (.branch 46 (.leaf (-21)) (.leaf (-20))))) (.branch 50 (.branch 48 (.leaf (-19)) (.branch 49 (.leaf (-18)) (.leaf (-17)))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-15)) (.leaf (-14)))))) (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_290_4961 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (7))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (5)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (8)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (4)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (6))) (.branch 23 (.leaf (3)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (7)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (4)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (8))) (.branch 40 (.leaf (1)) (.leaf (3))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (2))) (.branch 44 (.leaf (6)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (3))) (.branch 48 (.leaf (7)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (2))) (.branch 52 (.leaf (4)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (5))) (.branch 56 (.leaf (3)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (8)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (3)) (.leaf (6)))))))))
  code := certificateP9_4961
  counts := ![(.branch 31 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 50 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 58 (.branch 54 (.leaf (14)) (.leaf (15))) (.branch 61 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 30 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 59 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 31 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 34 (.leaf (-21)) (.branch 64 (.leaf (-26)) (.leaf (-30))))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))) (.branch 49 (.leaf (-5)) (.branch 53 (.leaf (-6)) (.leaf (-7))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 29 (.leaf (-4)) (.branch 62 (.leaf (-6)) (.leaf (-8))))),
  (.branch 14 (.branch 8 (.leaf (0)) (.leaf (-2))) (.branch 47 (.leaf (-10)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.branch 19 (.leaf (-27)) (.leaf (-28)))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 27 (.branch 6 (.leaf (0)) (.leaf (-17))) (.branch 48 (.leaf (-19)) (.leaf (-21)))),
  (.branch 15 (.leaf (0)) (.branch 60 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 65 (.leaf (-30)) (.leaf (-24))),
  (.branch 64 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-5)))),
  (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-5)))),
  (.branch 48 (.leaf (-15)) (.branch 57 (.leaf (-14)) (.leaf (-13)))),
  (.branch 59 (.branch 55 (.branch 53 (.leaf (-28)) (.branch 54 (.leaf (-26)) (.leaf (-24)))) (.branch 57 (.branch 56 (.leaf (-22)) (.leaf (-20))) (.branch 58 (.leaf (-18)) (.leaf (-16))))) (.branch 62 (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 57 (.branch 52 (.branch 50 (.branch 49 (.leaf (-21)) (.leaf (-20))) (.branch 51 (.leaf (-19)) (.leaf (-18)))) (.branch 54 (.branch 53 (.leaf (-17)) (.leaf (-16))) (.branch 55 (.leaf (-15)) (.branch 56 (.leaf (-14)) (.leaf (-13)))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-12)) (.leaf (-11))) (.branch 60 (.leaf (-10)) (.leaf (-9)))) (.branch 63 (.branch 62 (.leaf (-8)) (.leaf (-7))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-5)) (.leaf (-4))))))),
  (.branch 63 (.branch 61 (.leaf (-9)) (.branch 62 (.leaf (-8)) (.leaf (-7)))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-5)) (.leaf (-4)))))]
def witnessP9_290_4962 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (7))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (5))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (4))) (.branch 15 (.leaf (1)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (0))) (.branch 19 (.leaf (3)) (.leaf (7)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (8))) (.branch 27 (.leaf (6)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (5)) (.leaf (7)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (4)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (6)) (.leaf (8))) (.branch 40 (.leaf (0)) (.leaf (3))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (5))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (7)) (.leaf (4))) (.branch 48 (.leaf (1)) (.leaf (6)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (3)) (.leaf (8)))) (.branch 55 (.branch 54 (.leaf (5)) (.leaf (1))) (.branch 56 (.leaf (0)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (4)) (.leaf (7))) (.branch 60 (.leaf (6)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (3))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (5)) (.leaf (8)))))))))
  code := certificateP9_4962
  counts := ![(.branch 29 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 53 (.leaf (3)) (.branch 66 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-23))) (.branch 28 (.leaf (-24)) (.leaf (-25)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-36))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (-1))) (.branch 39 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 63 (.branch 57 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 63 (.branch 62 (.leaf (-25)) (.leaf (-20))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 58 (.branch 51 (.leaf (-14)) (.leaf (-12))) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 62 (.branch 60 (.branch 7 (.leaf (-36)) (.leaf (-35))) (.branch 61 (.leaf (-30)) (.leaf (-25)))) (.branch 64 (.branch 63 (.leaf (-20)) (.leaf (-15))) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 40 (.leaf (-3)) (.leaf (0)))]
def witnessP9_290_4963 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (8))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (5))) (.branch 15 (.leaf (2)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (8)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (5)) (.leaf (3)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (7))) (.branch 40 (.leaf (1)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (6)) (.leaf (2))) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (5))) (.branch 48 (.leaf (0)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (8)) (.leaf (0))) (.branch 52 (.leaf (2)) (.leaf (6)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (4))) (.branch 56 (.leaf (3)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (5)) (.leaf (1))) (.branch 60 (.leaf (0)) (.leaf (7)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (0))) (.branch 64 (.leaf (6)) (.branch 65 (.leaf (3)) (.leaf (4)))))))))
  code := certificateP9_4963
  counts := ![(.branch 32 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))) (.branch 48 (.branch 38 (.branch 35 (.leaf (11)) (.leaf (12))) (.branch 41 (.leaf (13)) (.branch 45 (.leaf (14)) (.leaf (15))))) (.branch 57 (.branch 51 (.leaf (16)) (.branch 54 (.leaf (17)) (.leaf (18)))) (.branch 60 (.leaf (19)) (.branch 63 (.leaf (20)) (.leaf (21))))))),
  (.branch 30 (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 34 (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.leaf (7))))),
  (.branch 37 (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 65 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 39 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 16 (.branch 13 (.leaf (-18)) (.leaf (-19))) (.branch 19 (.leaf (-20)) (.leaf (-21))))),
  (.branch 2 (.leaf (0)) (.branch 30 (.leaf (-52)) (.leaf (-54)))),
  (.branch 5 (.leaf (0)) (.branch 52 (.leaf (-31)) (.leaf (-32)))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 17 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-14)) (.leaf (-7)))),
  (.branch 61 (.branch 50 (.branch 31 (.leaf (-54)) (.leaf (-53))) (.branch 60 (.leaf (-49)) (.leaf (-42)))) (.branch 63 (.branch 62 (.leaf (-35)) (.leaf (-28))) (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-14)) (.leaf (-7)))))),
  (.branch 63 (.branch 53 (.leaf (-32)) (.leaf (-28))) (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-14)) (.leaf (-7))))),
  (.branch 28 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 65 (.leaf (-2)) (.leaf (-1))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_290_4964 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (5))) (.branch 15 (.leaf (3)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (6)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (8)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (7)) (.branch 32 (.leaf (3)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (5)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (6))) (.branch 40 (.leaf (3)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (8)) (.leaf (1))) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (5))) (.branch 48 (.leaf (3)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (6)) (.leaf (1))) (.branch 52 (.leaf (0)) (.leaf (7)))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (4))) (.branch 56 (.leaf (0)) (.leaf (3))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (5)) (.leaf (1))) (.branch 60 (.leaf (0)) (.leaf (6)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (0))) (.branch 64 (.leaf (8)) (.branch 65 (.leaf (3)) (.leaf (4)))))))))
  code := certificateP9_4964
  counts := ![(.branch 30 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-9)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-25))) (.branch 18 (.leaf (-26)) (.branch 26 (.leaf (-27)) (.leaf (-28))))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 20 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.branch 60 (.leaf (-28)) (.branch 61 (.leaf (-24)) (.leaf (-20)))) (.branch 64 (.branch 63 (.leaf (-16)) (.leaf (-12))) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 63 (.branch 38 (.leaf (-17)) (.leaf (-16))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 49 (.leaf (-6)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 65 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_290_4965 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (8))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (6))) (.branch 23 (.leaf (7)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (2)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (8)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (6)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (4)) (.leaf (0))) (.branch 40 (.leaf (1)) (.leaf (7))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (5)) (.leaf (2))) (.branch 44 (.leaf (0)) (.leaf (3)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (8))) (.branch 48 (.leaf (0)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (6)) (.leaf (1))) (.branch 52 (.leaf (4)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (5))) (.branch 56 (.leaf (7)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (3))) (.branch 60 (.leaf (2)) (.leaf (6)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (0))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (8)) (.leaf (4)))))))))
  code := certificateP9_4965
  counts := ![(.branch 30 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 48 (.branch 39 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 66 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 61 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-26)) (.leaf (-27)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 31 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 64 (.leaf (-9)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.branch 45 (.leaf (-17)) (.leaf (-18)))),
  (.branch 12 (.leaf (0)) (.branch 38 (.leaf (-3)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 28 (.leaf (-21)) (.leaf (-25)))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (-9))) (.branch 61 (.leaf (-10)) (.leaf (-13)))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (-9))) (.branch 56 (.leaf (-11)) (.leaf (-12)))),
  (.branch 14 (.leaf (0)) (.branch 47 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 59 (.branch 49 (.leaf (-27)) (.branch 54 (.leaf (-25)) (.leaf (-23)))) (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-14)) (.leaf (-7))))),
  (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 65 (.leaf (-12)) (.leaf (-9))),
  (.branch 62 (.branch 60 (.branch 46 (.leaf (-18)) (.leaf (-17))) (.branch 61 (.leaf (-15)) (.leaf (-13)))) (.branch 64 (.branch 63 (.leaf (-11)) (.leaf (-9))) (.branch 65 (.leaf (-7)) (.leaf (-5))))),
  (.branch 53 (.branch 39 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-2)) (.leaf (0)))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-25)) (.leaf (-23))) (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-19)) (.leaf (-17))))) (.branch 63 (.branch 61 (.leaf (-15)) (.branch 62 (.leaf (-13)) (.leaf (-11)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-7)) (.leaf (-5)))))),
  (.branch 63 (.branch 62 (.leaf (-13)) (.leaf (-11))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-7)) (.leaf (-5))))),
  (.branch 61 (.branch 58 (.branch 57 (.leaf (-12)) (.leaf (-11))) (.branch 59 (.leaf (-10)) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 63 (.branch 62 (.leaf (-7)) (.leaf (-6))) (.branch 64 (.leaf (-5)) (.branch 65 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 48 (.leaf (-4)) (.leaf (-3)))]
def witnessP9_290_4966 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (7)) (.leaf (1))) (.branch 15 (.leaf (5)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (0))) (.branch 19 (.leaf (6)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (8)) (.leaf (3))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (1))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (7))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (1)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (5)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (8)) (.leaf (4))) (.branch 40 (.leaf (0)) (.leaf (2))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (6)) (.leaf (1))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (7)) (.leaf (2))) (.branch 48 (.leaf (5)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (4)) (.leaf (0))) (.branch 52 (.leaf (6)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (8)) (.leaf (3))) (.branch 56 (.leaf (1)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (5)) (.leaf (2))) (.branch 60 (.leaf (4)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (7))) (.branch 64 (.leaf (6)) (.branch 65 (.leaf (2)) (.leaf (3)))))))))
  code := certificateP9_4966
  counts := ![(.branch 28 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 56 (.leaf (9)) (.branch 62 (.leaf (10)) (.leaf (11)))))),
  (.branch 35 (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))) (.branch 53 (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))) (.branch 59 (.leaf (9)) (.branch 65 (.leaf (10)) (.leaf (11)))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-23))) (.branch 28 (.leaf (-24)) (.branch 61 (.leaf (-28)) (.leaf (-31))))),
  (.branch 2 (.leaf (0)) (.branch 37 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 27 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (-2)) (.leaf (-3)))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (-23)) (.leaf (-24))))]
  high := ![(.branch 63 (.branch 62 (.leaf (-31)) (.leaf (-26))) (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-16)) (.leaf (-11))))),
  (.branch 63 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 64 (.branch 47 (.leaf (-7)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 60 (.branch 57 (.branch 55 (.leaf (-24)) (.branch 56 (.leaf (-22)) (.leaf (-20)))) (.branch 58 (.leaf (-18)) (.branch 59 (.leaf (-16)) (.leaf (-14))))) (.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-10)) (.leaf (-8)))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))))]
def witnessP9_290_4967 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (7))) (.branch 7 (.leaf (2)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (0))) (.branch 11 (.leaf (8)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (5))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (8))) (.branch 23 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (2))) (.branch 27 (.leaf (4)) (.leaf (7)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (3)) (.leaf (8)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (5)) (.leaf (4)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (7))) (.branch 40 (.leaf (1)) (.leaf (3))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (6)) (.leaf (0))) (.branch 44 (.leaf (8)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (0)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (7)) (.leaf (3))) (.branch 52 (.leaf (0)) (.leaf (6)))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (8))) (.branch 56 (.leaf (4)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (5)) (.leaf (1))) (.branch 60 (.leaf (3)) (.leaf (7)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (2))) (.branch 64 (.leaf (6)) (.branch 65 (.leaf (4)) (.leaf (8)))))))))
  code := certificateP9_4967
  counts := ![(.branch 29 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 48 (.branch 38 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 43 (.leaf (9)) (.leaf (10)))) (.branch 57 (.branch 52 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 30 (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.leaf (7))))),
  (.branch 37 (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 65 (.leaf (6)) (.leaf (7))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-26))) (.branch 19 (.leaf (-31)) (.leaf (-32)))),
  (.branch 2 (.leaf (0)) (.branch 30 (.leaf (-52)) (.leaf (-54)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (-17))) (.branch 63 (.leaf (-20)) (.leaf (-21)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-38))) (.branch 41 (.leaf (-41)) (.leaf (-43)))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 63 (.branch 53 (.leaf (-32)) (.branch 58 (.leaf (-30)) (.leaf (-28)))) (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-14)) (.leaf (-7))))),
  (.branch 61 (.branch 50 (.branch 31 (.leaf (-54)) (.leaf (-53))) (.branch 60 (.leaf (-49)) (.leaf (-42)))) (.branch 63 (.branch 62 (.leaf (-35)) (.leaf (-28))) (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-14)) (.leaf (-7)))))),
  (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-14)) (.leaf (-7)))),
  (.branch 62 (.branch 42 (.leaf (-43)) (.branch 61 (.leaf (-42)) (.leaf (-35)))) (.branch 64 (.branch 63 (.leaf (-28)) (.leaf (-21))) (.branch 65 (.leaf (-14)) (.leaf (-7))))),
  (.branch 28 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.leaf (-7)))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 65 (.leaf (-2)) (.leaf (-1))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessP9_290_4968 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (6)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (8)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (5))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (7)) (.leaf (2))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (8))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (2)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (5)) (.leaf (3))) (.branch 36 (.leaf (0)) (.leaf (6)))) (.branch 39 (.branch 38 (.leaf (4)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (7)) (.leaf (3))) (.branch 44 (.leaf (5)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (8))) (.branch 48 (.leaf (2)) (.leaf (4)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (3))) (.branch 52 (.leaf (6)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (2))) (.branch 56 (.leaf (5)) (.leaf (3))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (7))) (.branch 60 (.leaf (4)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (0))) (.branch 64 (.leaf (8)) (.branch 65 (.leaf (3)) (.leaf (5)))))))))
  code := certificateP9_4968
  counts := ![(.branch 32 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 50 (.branch 41 (.branch 36 (.leaf (8)) (.leaf (9))) (.branch 45 (.leaf (10)) (.leaf (11)))) (.branch 58 (.branch 54 (.leaf (12)) (.leaf (13))) (.branch 63 (.leaf (14)) (.leaf (15)))))),
  (.branch 31 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 33 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 12 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 14 (.leaf (-17)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-16)) (.leaf (-17)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 18 (.leaf (-11)) (.leaf (-12)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 35 (.leaf (-4)) (.branch 57 (.leaf (-5)) (.leaf (-6))))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 52 (.leaf (-41)) (.leaf (-44)))),
  (.branch 8 (.leaf (0)) (.leaf (-26))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (-5)) (.leaf (-10))))]
  high := ![(.branch 64 (.branch 59 (.leaf (-18)) (.leaf (-15))) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.branch 63 (.branch 54 (.leaf (-17)) (.branch 62 (.leaf (-15)) (.leaf (-12)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 64 (.branch 63 (.leaf (-12)) (.leaf (-9))) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 58 (.leaf (-6)) (.leaf (-5))),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 59 (.branch 55 (.branch 53 (.leaf (-44)) (.branch 54 (.leaf (-41)) (.leaf (-38)))) (.branch 57 (.branch 56 (.leaf (-35)) (.leaf (-32))) (.branch 58 (.leaf (-29)) (.leaf (-26))))) (.branch 62 (.branch 60 (.leaf (-23)) (.branch 61 (.leaf (-20)) (.leaf (-17)))) (.branch 64 (.branch 63 (.leaf (-14)) (.leaf (-11))) (.branch 65 (.leaf (-8)) (.leaf (-5)))))),
  (.branch 61 (.branch 26 (.branch 9 (.leaf (-26)) (.leaf (-25))) (.branch 43 (.leaf (-24)) (.branch 60 (.leaf (-23)) (.leaf (-20))))) (.branch 63 (.branch 62 (.leaf (-17)) (.leaf (-14))) (.branch 64 (.leaf (-11)) (.branch 65 (.leaf (-8)) (.leaf (-5)))))),
  (.branch 48 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-5))))]
def witnessP9_290_4969 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (6)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (8))) (.branch 15 (.leaf (3)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (4)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (7)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (8)) (.branch 32 (.leaf (1)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (6)) (.leaf (3)))) (.branch 39 (.branch 38 (.leaf (5)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (4))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (7)) (.leaf (2))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (8))) (.branch 48 (.leaf (4)) (.leaf (5)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (3)) (.leaf (6)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (4))) (.branch 56 (.leaf (0)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (7)) (.leaf (3))) (.branch 60 (.leaf (5)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (4))) (.branch 64 (.leaf (8)) (.branch 65 (.leaf (2)) (.leaf (3)))))))))
  code := certificateP9_4969
  counts := ![(.branch 29 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 54 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 37 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 44 (.leaf (5)) (.leaf (6))) (.branch 59 (.leaf (7)) (.branch 66 (.leaf (8)) (.leaf (9)))))),
  (.branch 33 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 41 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 63 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.leaf (-16))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-27))),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 63 (.branch 57 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 63 (.branch 47 (.leaf (-16)) (.branch 62 (.leaf (-15)) (.leaf (-12)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 58 (.leaf (-5)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 64 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.branch 55 (.branch 37 (.leaf (-27)) (.branch 54 (.leaf (-26)) (.leaf (-24)))) (.branch 57 (.branch 56 (.leaf (-22)) (.leaf (-20))) (.branch 58 (.leaf (-18)) (.leaf (-16))))) (.branch 62 (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-16)) (.leaf (-14))) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 48 (.leaf (-5)) (.branch 65 (.leaf (-4)) (.leaf (-2))))]
def witnessP9_290_4970 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (6)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (3)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (8)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (7)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (8)) (.leaf (5))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (6))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (7)) (.leaf (2))) (.branch 36 (.leaf (0)) (.leaf (5)))) (.branch 39 (.branch 38 (.leaf (8)) (.leaf (1))) (.branch 40 (.leaf (3)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (6))) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (7))) (.branch 48 (.leaf (5)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (3))) (.branch 52 (.leaf (8)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (4))) (.branch 56 (.leaf (6)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (5))) (.branch 60 (.leaf (7)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (3)) (.leaf (0))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (8)) (.leaf (4)))))))))
  code := certificateP9_4970
  counts := ![(.branch 32 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 49 (.branch 41 (.branch 36 (.leaf (8)) (.leaf (9))) (.branch 45 (.leaf (10)) (.leaf (11)))) (.branch 58 (.branch 54 (.leaf (12)) (.leaf (13))) (.branch 63 (.leaf (14)) (.leaf (15)))))),
  (.branch 31 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 65 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-16)) (.leaf (-17)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 20 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-51)) (.leaf (-52)))),
  (.branch 34 (.branch 8 (.leaf (0)) (.branch 21 (.leaf (-26)) (.leaf (-27)))) (.branch 47 (.leaf (-28)) (.branch 60 (.leaf (-29)) (.leaf (-30))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (-6))) (.branch 38 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 59 (.branch 50 (.leaf (-19)) (.leaf (-18))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 63 (.branch 54 (.leaf (-17)) (.branch 62 (.leaf (-15)) (.leaf (-12)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 65 (.leaf (-6)) (.leaf (-3))),
  (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 57 (.branch 17 (.leaf (-52)) (.leaf (-50))) (.branch 58 (.leaf (-45)) (.branch 59 (.leaf (-40)) (.leaf (-35))))) (.branch 63 (.branch 61 (.leaf (-30)) (.branch 62 (.leaf (-25)) (.leaf (-20)))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 63 (.branch 61 (.leaf (-30)) (.branch 62 (.leaf (-25)) (.leaf (-20)))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 39 (.leaf (-8)) (.leaf (-5)))]
def witnessP9_290_4971 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (7)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (8)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (5)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (3)) (.leaf (1))) (.branch 19 (.leaf (6)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (0))) (.branch 23 (.leaf (2)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (7)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (4)) (.leaf (6)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (8)) (.leaf (5)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (1)) (.leaf (2))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (4))) (.branch 44 (.leaf (7)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (2))) (.branch 48 (.leaf (5)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (3)) (.leaf (1))) (.branch 52 (.leaf (6)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (4)) (.leaf (0))) (.branch 56 (.leaf (2)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (8)) (.leaf (0))) (.branch 60 (.leaf (5)) (.leaf (3)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (0))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (4)) (.leaf (6)))))))))
  code := certificateP9_4971
  counts := ![(.branch 30 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 55 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 29 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 16 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 22 (.leaf (-19)) (.branch 55 (.leaf (-29)) (.leaf (-38))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 12 (.leaf (-8)) (.leaf (-9)))),
  (.branch 31 (.branch 8 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-4)))) (.branch 47 (.leaf (-5)) (.branch 64 (.leaf (-7)) (.leaf (-8))))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 33 (.leaf (0)) (.leaf (-3))),
  (.branch 25 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 44 (.leaf (-23)) (.leaf (-28)))),
  (.branch 11 (.leaf (0)) (.branch 58 (.leaf (-13)) (.leaf (-14))))]
  high := ![(.branch 60 (.branch 56 (.leaf (-38)) (.leaf (-37))) (.branch 64 (.leaf (-36)) (.branch 65 (.leaf (-30)) (.leaf (-24))))),
  (.branch 63 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 65 (.leaf (-8)) (.leaf (-7))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 62 (.branch 49 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 34 (.leaf (-3)) (.leaf (-2))) (.branch 54 (.leaf (-1)) (.leaf (0)))),
  (.branch 55 (.branch 49 (.branch 46 (.branch 45 (.leaf (-28)) (.leaf (-27))) (.branch 47 (.leaf (-26)) (.branch 48 (.leaf (-25)) (.leaf (-24))))) (.branch 52 (.branch 50 (.leaf (-23)) (.branch 51 (.leaf (-22)) (.leaf (-21)))) (.branch 53 (.leaf (-20)) (.branch 54 (.leaf (-19)) (.leaf (-18)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-17)) (.leaf (-16))) (.branch 58 (.leaf (-15)) (.branch 59 (.leaf (-14)) (.leaf (-13))))) (.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-11)) (.leaf (-10)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7))))))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-14)) (.leaf (-13))) (.branch 61 (.leaf (-12)) (.leaf (-11)))) (.branch 64 (.branch 63 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-7)))))]
def witnessP9_290_4972 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (1)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (8))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (5))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (6))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (1)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (7)) (.leaf (2))) (.branch 36 (.leaf (0)) (.leaf (5)))) (.branch 39 (.branch 38 (.leaf (3)) (.leaf (1))) (.branch 40 (.leaf (4)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (6)) (.leaf (2))) (.branch 44 (.leaf (8)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (1))) (.branch 48 (.leaf (5)) (.leaf (4)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (2))) (.branch 52 (.leaf (6)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (1))) (.branch 56 (.leaf (7)) (.leaf (4))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (5))) (.branch 60 (.leaf (2)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (3)) (.leaf (0))) (.branch 64 (.leaf (6)) (.branch 65 (.leaf (4)) (.leaf (8)))))))))
  code := certificateP9_4972
  counts := ![(.branch 31 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 50 (.branch 41 (.branch 36 (.leaf (8)) (.leaf (9))) (.branch 45 (.leaf (10)) (.leaf (11)))) (.branch 58 (.branch 53 (.leaf (12)) (.leaf (13))) (.branch 63 (.leaf (14)) (.leaf (15)))))),
  (.branch 33 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 31 (.leaf (-9)) (.branch 53 (.leaf (-10)) (.leaf (-11))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 39 (.leaf (-11)) (.branch 61 (.leaf (-12)) (.leaf (-13))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-25))) (.branch 18 (.leaf (-26)) (.leaf (-27)))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-13))) (.branch 21 (.leaf (-14)) (.branch 29 (.leaf (-15)) (.leaf (-16))))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 59 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-7)) (.leaf (-5))))),
  (.branch 63 (.branch 62 (.leaf (-13)) (.leaf (-11))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-7)) (.leaf (-5))))),
  (.branch 62 (.branch 52 (.leaf (-27)) (.branch 61 (.leaf (-24)) (.leaf (-20)))) (.branch 64 (.branch 63 (.leaf (-16)) (.leaf (-12))) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 64 (.branch 63 (.leaf (-16)) (.leaf (-12))) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.branch 41 (.leaf (-5)) (.leaf (-4))),
  (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 61 (.branch 58 (.branch 57 (.leaf (-10)) (.leaf (-9))) (.branch 59 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6))))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_290_4973 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (8))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (4))) (.branch 19 (.leaf (8)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (6))) (.branch 23 (.leaf (1)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (7)) (.leaf (5))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (8)) (.leaf (6)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (1)) (.leaf (5)))) (.branch 39 (.branch 38 (.leaf (2)) (.leaf (7))) (.branch 40 (.leaf (4)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (3)) (.leaf (1))) (.branch 44 (.leaf (6)) (.leaf (8)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (0))) (.branch 48 (.leaf (5)) (.leaf (3)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (1)) (.leaf (4))) (.branch 52 (.leaf (7)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (6))) (.branch 56 (.leaf (1)) (.leaf (3))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (8)) (.leaf (5))) (.branch 60 (.leaf (2)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (4)) (.leaf (1))) (.branch 64 (.leaf (3)) (.branch 65 (.leaf (7)) (.leaf (6)))))))))
  code := certificateP9_4973
  counts := ![(.branch 28 (.branch 8 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 36 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 60 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 39 (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 65 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 14 (.leaf (-28)) (.leaf (-29)))),
  (.branch 3 (.leaf (0)) (.leaf (-18))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-16))) (.branch 16 (.leaf (-17)) (.leaf (-18)))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (-6)) (.leaf (-7)))),
  (.branch 32 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-36)) (.leaf (-37)))) (.branch 45 (.leaf (-38)) (.branch 58 (.leaf (-39)) (.leaf (-40)))))]
  high := ![(.branch 62 (.branch 48 (.leaf (-29)) (.branch 55 (.leaf (-27)) (.leaf (-25)))) (.branch 64 (.branch 63 (.leaf (-20)) (.leaf (-15))) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 57 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 63 (.branch 61 (.leaf (-18)) (.branch 62 (.leaf (-15)) (.leaf (-12)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 50 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 26 (.leaf (-7)) (.leaf (-5))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-40)) (.leaf (-35))) (.branch 61 (.leaf (-30)) (.leaf (-25)))) (.branch 64 (.branch 63 (.leaf (-20)) (.leaf (-15))) (.branch 65 (.leaf (-10)) (.leaf (-5)))))]
def witnessP9_290_4974 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (4)) (.leaf (8))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (4))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (8))) (.branch 27 (.leaf (3)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (7)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (1)) (.leaf (6)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 40 (.leaf (4)) (.leaf (8))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (3))) (.branch 44 (.leaf (0)) (.leaf (5)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (3)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (7)) (.leaf (4))) (.branch 52 (.leaf (2)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (6)) (.leaf (1))) (.branch 56 (.leaf (3)) (.leaf (5))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (8))) (.branch 60 (.leaf (2)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (4)) (.leaf (0))) (.branch 64 (.leaf (3)) (.branch 65 (.leaf (7)) (.leaf (5)))))))))
  code := certificateP9_4974
  counts := ![(.branch 30 (.branch 11 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 48 (.branch 38 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 28 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 36 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 60 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 34 (.leaf (-5)) (.branch 38 (.leaf (-6)) (.leaf (-7))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 14 (.leaf (-5)) (.branch 47 (.leaf (-7)) (.leaf (-9))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 23 (.leaf (-21)) (.branch 52 (.leaf (-23)) (.leaf (-28))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-5)) (.leaf (-7)))) (.branch 49 (.leaf (-12)) (.branch 56 (.leaf (-14)) (.leaf (-16))))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 33 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-25))),
  (.branch 32 (.leaf (0)) (.branch 65 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.branch 41 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 64 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-5)))),
  (.branch 63 (.branch 62 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-5))))),
  (.branch 62 (.branch 53 (.leaf (-28)) (.branch 61 (.leaf (-27)) (.leaf (-24)))) (.branch 64 (.branch 63 (.leaf (-21)) (.leaf (-18))) (.branch 65 (.leaf (-15)) (.leaf (-12))))),
  (.branch 57 (.leaf (-16)) (.branch 65 (.leaf (-15)) (.leaf (-12)))),
  (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 34 (.leaf (-3)) (.leaf (-2))) (.branch 58 (.leaf (-1)) (.leaf (0)))),
  (.branch 59 (.branch 56 (.branch 38 (.leaf (-25)) (.branch 55 (.leaf (-24)) (.leaf (-22)))) (.branch 57 (.leaf (-20)) (.branch 58 (.leaf (-18)) (.leaf (-16))))) (.branch 62 (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (-3)),
  (.branch 62 (.branch 60 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.leaf (-7)))) (.branch 64 (.branch 63 (.leaf (-6)) (.leaf (-5))) (.branch 65 (.leaf (-4)) (.leaf (-3)))))]
def witnessP9_290_4975 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (4))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (7)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (1)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (3)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (4))) (.branch 40 (.leaf (2)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (6)) (.leaf (1))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (4))) (.branch 48 (.leaf (1)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (2))) (.branch 52 (.leaf (0)) (.leaf (3)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (4))) (.branch 56 (.leaf (0)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (8)) (.leaf (1))) (.branch 60 (.leaf (0)) (.leaf (3)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (0))) (.branch 64 (.leaf (4)) (.branch 65 (.leaf (1)) (.leaf (5)))))))))
  code := certificateP9_4975
  counts := ![(.branch 30 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 32 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 58 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-21)) (.leaf (-22)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-9))) (.branch 22 (.leaf (-10)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-24))),
  (.branch 25 (.leaf (0)) (.leaf (-41))),
  (.branch 58 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 60 (.leaf (-3)) (.leaf (-2))),
  (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 63 (.branch 45 (.leaf (-22)) (.branch 62 (.leaf (-20)) (.leaf (-16)))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 56 (.leaf (-11)) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 54 (.branch 48 (.branch 45 (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22)))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19))))) (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 35 (.branch 30 (.branch 27 (.branch 26 (.leaf (-41)) (.leaf (-40))) (.branch 28 (.leaf (-39)) (.branch 29 (.leaf (-38)) (.leaf (-37))))) (.branch 32 (.branch 31 (.leaf (-36)) (.leaf (-35))) (.branch 33 (.leaf (-34)) (.branch 34 (.leaf (-33)) (.leaf (-32)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-31)) (.leaf (-30))) (.branch 38 (.leaf (-29)) (.branch 39 (.leaf (-28)) (.leaf (-27))))) (.branch 42 (.branch 41 (.leaf (-26)) (.leaf (-25))) (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22))))))) (.branch 55 (.branch 50 (.branch 47 (.branch 46 (.leaf (-21)) (.leaf (-20))) (.branch 48 (.leaf (-19)) (.branch 49 (.leaf (-18)) (.leaf (-17))))) (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_290_4976 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (5))) (.branch 7 (.leaf (0)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (6))) (.branch 15 (.leaf (2)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (0))) (.branch 19 (.leaf (3)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (8))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (6)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (4)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (2)) (.leaf (5))) (.branch 40 (.leaf (0)) (.leaf (7))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (3)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (4)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (6))) (.branch 48 (.leaf (3)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (0))) (.branch 52 (.leaf (2)) (.leaf (4)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (8))) (.branch 56 (.leaf (3)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (6)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (5)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (4))) (.branch 64 (.leaf (3)) (.branch 65 (.leaf (1)) (.leaf (6)))))))))
  code := certificateP9_4976
  counts := ![(.branch 29 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 60 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 30 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 14 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 58 (.branch 47 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 15 (.leaf (-19)) (.branch 44 (.leaf (-24)) (.leaf (-29))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-8))) (.branch 48 (.leaf (-13)) (.leaf (-17)))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 36 (.leaf (-7)) (.branch 53 (.leaf (-9)) (.leaf (-10))))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 33 (.branch 25 (.leaf (0)) (.leaf (-1))) (.branch 58 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.leaf (-25))),
  (.branch 22 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 63 (.branch 35 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 60 (.leaf (-3)) (.leaf (-2))),
  (.branch 62 (.branch 53 (.branch 45 (.leaf (-29)) (.leaf (-28))) (.branch 61 (.leaf (-27)) (.leaf (-24)))) (.branch 64 (.branch 63 (.leaf (-21)) (.leaf (-18))) (.branch 65 (.leaf (-15)) (.leaf (-12))))),
  (.branch 57 (.branch 49 (.leaf (-17)) (.leaf (-16))) (.branch 65 (.leaf (-15)) (.leaf (-12)))),
  (.branch 64 (.branch 54 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-7)))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-7)) (.leaf (-6))) (.branch 61 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.branch 63 (.leaf (-3)) (.leaf (-2))) (.branch 65 (.leaf (-1)) (.leaf (0))))),
  (.branch 53 (.branch 47 (.branch 44 (.branch 42 (.leaf (-25)) (.branch 43 (.leaf (-24)) (.leaf (-23)))) (.branch 45 (.leaf (-22)) (.branch 46 (.leaf (-21)) (.leaf (-20))))) (.branch 50 (.branch 48 (.leaf (-19)) (.branch 49 (.leaf (-18)) (.leaf (-17)))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-15)) (.leaf (-14)))))) (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_290_4977 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (5))) (.branch 15 (.leaf (1)) (.leaf (7)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (0))) (.branch 19 (.leaf (4)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (5))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (1))) (.branch 27 (.leaf (4)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (5))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (8)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (4)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (5)) (.leaf (2))) (.branch 40 (.leaf (0)) (.leaf (6))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (3)) (.leaf (1))) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (5))) (.branch 48 (.leaf (1)) (.leaf (7)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (3)) (.leaf (0))) (.branch 52 (.leaf (4)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (5))) (.branch 56 (.leaf (0)) (.leaf (3))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (6)) (.leaf (1))) (.branch 60 (.leaf (4)) (.leaf (2)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (5))) (.branch 64 (.leaf (3)) (.branch 65 (.leaf (1)) (.leaf (8)))))))))
  code := certificateP9_4977
  counts := ![(.branch 29 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2)))),
  (.branch 33 (.leaf (0)) (.branch 66 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-16)) (.leaf (-17)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 20 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 19 (.leaf (-22)) (.branch 27 (.leaf (-23)) (.leaf (-24))))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.leaf (0)) (.leaf (-17))),
  (.branch 16 (.leaf (0)) (.leaf (-17))),
  (.leaf (0))]
  high := ![(.branch 63 (.branch 57 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 60 (.leaf (-3)) (.leaf (-2))),
  (.branch 63 (.branch 54 (.leaf (-17)) (.branch 62 (.leaf (-15)) (.leaf (-12)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 65 (.leaf (-6)) (.leaf (-3))),
  (.branch 63 (.branch 61 (.leaf (-24)) (.branch 62 (.leaf (-20)) (.leaf (-16)))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 64 (.branch 39 (.leaf (-13)) (.leaf (-12))) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.branch 61 (.branch 59 (.branch 42 (.leaf (-17)) (.leaf (-16))) (.branch 60 (.leaf (-14)) (.leaf (-12)))) (.branch 63 (.branch 62 (.leaf (-10)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))) (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.leaf (-10))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_290_4978 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (6))) (.branch 15 (.leaf (1)) (.leaf (8)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (0))) (.branch 19 (.leaf (4)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (5))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (7)) (.leaf (1))) (.branch 27 (.leaf (4)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (6))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (8)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (4)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (5)) (.leaf (2))) (.branch 40 (.leaf (0)) (.leaf (7))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (3)) (.leaf (1))) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (6))) (.branch 48 (.leaf (1)) (.leaf (8)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (3)) (.leaf (0))) (.branch 52 (.leaf (4)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (5))) (.branch 56 (.leaf (0)) (.leaf (3))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (7)) (.leaf (1))) (.branch 60 (.leaf (4)) (.leaf (2)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (6))) (.branch 64 (.leaf (3)) (.branch 65 (.leaf (1)) (.leaf (8)))))))))
  code := certificateP9_4978
  counts := ![(.branch 29 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-16)) (.leaf (-17)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 20 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 19 (.leaf (-22)) (.branch 27 (.leaf (-23)) (.leaf (-24))))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 14 (.leaf (0)) (.branch 30 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-17))),
  (.branch 16 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 63 (.branch 57 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 60 (.leaf (-3)) (.leaf (-2))),
  (.branch 63 (.branch 54 (.leaf (-17)) (.branch 62 (.leaf (-15)) (.leaf (-12)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 65 (.leaf (-6)) (.leaf (-3))),
  (.branch 63 (.branch 61 (.leaf (-24)) (.branch 62 (.leaf (-20)) (.leaf (-16)))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 60 (.branch 57 (.branch 39 (.leaf (-23)) (.branch 56 (.leaf (-22)) (.leaf (-20)))) (.branch 58 (.leaf (-18)) (.branch 59 (.leaf (-16)) (.leaf (-14))))) (.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-10)) (.leaf (-8)))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 61 (.branch 59 (.branch 42 (.leaf (-17)) (.leaf (-16))) (.branch 60 (.leaf (-14)) (.leaf (-12)))) (.branch 63 (.branch 62 (.leaf (-10)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 50 (.leaf (-1)) (.leaf (0)))]
def witnessP9_290_4979 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (6)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (7))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (2))) (.branch 11 (.leaf (8)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (6))) (.branch 15 (.leaf (4)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (2))) (.branch 19 (.leaf (1)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (8))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (2))) (.branch 27 (.leaf (1)) (.leaf (7)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (4)) (.leaf (8)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (1)) (.leaf (2))) (.branch 36 (.leaf (6)) (.leaf (3)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (7))) (.branch 40 (.leaf (4)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (5)) (.leaf (2))) (.branch 44 (.leaf (8)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (6))) (.branch 48 (.leaf (4)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (7)) (.leaf (2))) (.branch 52 (.leaf (0)) (.leaf (5)))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (8))) (.branch 56 (.leaf (1)) (.leaf (4))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (6)) (.leaf (2))) (.branch 60 (.leaf (0)) (.leaf (7)))) (.branch 63 (.branch 62 (.leaf (3)) (.leaf (1))) (.branch 64 (.leaf (5)) (.branch 65 (.leaf (4)) (.leaf (8)))))))))
  code := certificateP9_4979
  counts := ![(.branch 30 (.branch 8 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 60 (.leaf (8)) (.leaf (9)))))),
  (.branch 34 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 41 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 63 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-19)) (.leaf (-20)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 19 (.leaf (-8)) (.leaf (-9)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-25))) (.branch 18 (.leaf (-26)) (.branch 26 (.leaf (-27)) (.leaf (-28))))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 62 (.branch 53 (.leaf (-20)) (.branch 61 (.leaf (-18)) (.leaf (-15)))) (.branch 64 (.branch 63 (.leaf (-12)) (.leaf (-9))) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.branch 60 (.leaf (-28)) (.branch 61 (.leaf (-24)) (.leaf (-20)))) (.branch 64 (.branch 63 (.leaf (-16)) (.leaf (-12))) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 63 (.branch 38 (.leaf (-17)) (.leaf (-16))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 49 (.leaf (-6)) (.leaf (-4))),
  (.branch 65 (.leaf (-2)) (.leaf (-1))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessP9_290_4980 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (7)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (1))) (.branch 11 (.leaf (6)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (8))) (.branch 19 (.leaf (2)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (6))) (.branch 23 (.leaf (1)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (5))) (.branch 27 (.leaf (0)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (7)) (.leaf (1))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (2)) (.leaf (6)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (4))) (.branch 36 (.leaf (1)) (.leaf (5)))) (.branch 39 (.branch 38 (.leaf (3)) (.leaf (2))) (.branch 40 (.leaf (8)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (4)) (.leaf (1))) (.branch 44 (.leaf (6)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (0))) (.branch 48 (.leaf (5)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (4)) (.leaf (7))) (.branch 52 (.leaf (2)) (.leaf (3)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (6))) (.branch 56 (.leaf (1)) (.leaf (4))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (2)) (.leaf (5))) (.branch 60 (.leaf (3)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (8)) (.leaf (1))) (.branch 64 (.leaf (4)) (.branch 65 (.leaf (2)) (.leaf (6)))))))))
  code := certificateP9_4980
  counts := ![(.branch 27 (.branch 8 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 36 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 39 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 65 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 60 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.leaf (-28))) (.branch 27 (.leaf (-29)) (.leaf (-30)))),
  (.branch 3 (.leaf (0)) (.branch 49 (.leaf (-18)) (.leaf (-19)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-16))) (.branch 16 (.leaf (-17)) (.leaf (-18)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 20 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 18 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 62 (.branch 48 (.branch 28 (.leaf (-30)) (.leaf (-29))) (.branch 55 (.leaf (-27)) (.leaf (-25)))) (.branch 64 (.branch 63 (.leaf (-20)) (.leaf (-15))) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 57 (.branch 50 (.leaf (-19)) (.leaf (-17))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 6 (.leaf (-8)) (.branch 59 (.leaf (-7)) (.leaf (-5)))),
  (.branch 63 (.branch 61 (.leaf (-18)) (.branch 62 (.leaf (-15)) (.leaf (-12)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 65 (.leaf (-6)) (.leaf (-3))),
  (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 58 (.branch 54 (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_290_4981 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (2))) (.branch 15 (.leaf (8)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (7))) (.branch 27 (.leaf (0)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (8)) (.branch 32 (.leaf (1)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (2)) (.leaf (6)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (5))) (.branch 40 (.leaf (1)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (7)) (.leaf (2))) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (1))) (.branch 48 (.leaf (8)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (2))) (.branch 52 (.leaf (0)) (.leaf (6)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (4))) (.branch 56 (.leaf (0)) (.leaf (3))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (2)) (.leaf (7))) (.branch 60 (.leaf (0)) (.leaf (5)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (0))) (.branch 64 (.leaf (8)) (.branch 65 (.leaf (2)) (.leaf (4)))))))))
  code := certificateP9_4981
  counts := ![(.branch 30 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 32 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 54 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 2 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-25)) (.leaf (-26)))),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.branch 31 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 63 (.branch 55 (.leaf (-14)) (.leaf (-12))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.branch 56 (.branch 54 (.leaf (-26)) (.branch 55 (.leaf (-24)) (.leaf (-22)))) (.branch 57 (.leaf (-20)) (.branch 58 (.leaf (-18)) (.leaf (-16))))) (.branch 62 (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 62 (.branch 60 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 65 (.leaf (-4)) (.leaf (-2)))]
def witnessP9_290_4982 : CycleWitness 9 where
  length := 65
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (0))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (0)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (6))) (.branch 35 (.leaf (1)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (0))) (.branch 39 (.leaf (3)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (2)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (3)) (.leaf (0))) (.branch 47 (.leaf (7)) (.leaf (1)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (0)) (.leaf (8)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (2)) (.branch 64 (.leaf (0)) (.leaf (3)))))))))
  code := certificateP9_4982
  counts := ![(.branch 31 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 18 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 20 (.leaf (9)) (.leaf (10)))) (.branch 27 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 29 (.leaf (13)) (.leaf (14)))))) (.branch 49 (.branch 40 (.branch 36 (.branch 33 (.leaf (15)) (.leaf (16))) (.branch 38 (.leaf (17)) (.leaf (18)))) (.branch 44 (.branch 42 (.leaf (19)) (.leaf (20))) (.branch 46 (.leaf (21)) (.leaf (22))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (23)) (.leaf (24))) (.branch 55 (.leaf (25)) (.leaf (26)))) (.branch 62 (.branch 59 (.leaf (27)) (.leaf (28))) (.branch 64 (.leaf (29)) (.leaf (30))))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 37 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 39 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 65 (.leaf (9)) (.leaf (10)))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1))),
  (.branch 60 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-8)) (.branch 7 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-57))),
  (.branch 21 (.leaf (0)) (.leaf (-44))),
  (.branch 34 (.leaf (0)) (.leaf (-31))),
  (.branch 47 (.leaf (0)) (.leaf (-18))),
  (.branch 60 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 60 (.leaf (-10)) (.leaf (-6))),
  (.branch 62 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-4)) (.leaf (-2))))),
  (.branch 57 (.leaf (-5)) (.branch 64 (.leaf (-4)) (.leaf (-2)))),
  (.branch 59 (.leaf (-1)) (.leaf (0))),
  (.branch 36 (.branch 22 (.branch 15 (.branch 11 (.branch 9 (.leaf (-57)) (.branch 10 (.leaf (-56)) (.leaf (-55)))) (.branch 13 (.branch 12 (.leaf (-54)) (.leaf (-53))) (.branch 14 (.leaf (-52)) (.leaf (-51))))) (.branch 18 (.branch 16 (.leaf (-50)) (.branch 17 (.leaf (-49)) (.leaf (-48)))) (.branch 20 (.branch 19 (.leaf (-47)) (.leaf (-46))) (.branch 21 (.leaf (-45)) (.leaf (-44)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-43)) (.branch 24 (.leaf (-42)) (.leaf (-41)))) (.branch 27 (.branch 26 (.leaf (-40)) (.leaf (-39))) (.branch 28 (.leaf (-38)) (.leaf (-37))))) (.branch 32 (.branch 30 (.leaf (-36)) (.branch 31 (.leaf (-35)) (.leaf (-34)))) (.branch 34 (.branch 33 (.leaf (-33)) (.leaf (-32))) (.branch 35 (.leaf (-31)) (.leaf (-30))))))) (.branch 50 (.branch 43 (.branch 39 (.branch 37 (.leaf (-29)) (.branch 38 (.leaf (-28)) (.leaf (-27)))) (.branch 41 (.branch 40 (.leaf (-26)) (.leaf (-25))) (.branch 42 (.leaf (-24)) (.leaf (-23))))) (.branch 46 (.branch 44 (.leaf (-22)) (.branch 45 (.leaf (-21)) (.leaf (-20)))) (.branch 48 (.branch 47 (.leaf (-19)) (.leaf (-18))) (.branch 49 (.leaf (-17)) (.leaf (-16)))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (-15)) (.branch 52 (.leaf (-14)) (.leaf (-13)))) (.branch 55 (.branch 54 (.leaf (-12)) (.leaf (-11))) (.branch 56 (.leaf (-10)) (.leaf (-9))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-8)) (.leaf (-7))) (.branch 60 (.leaf (-6)) (.leaf (-5)))) (.branch 63 (.branch 62 (.leaf (-4)) (.leaf (-3))) (.branch 64 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (-44)) (.leaf (-43))) (.branch 24 (.leaf (-42)) (.branch 25 (.leaf (-41)) (.leaf (-40))))) (.branch 29 (.branch 27 (.leaf (-39)) (.branch 28 (.leaf (-38)) (.leaf (-37)))) (.branch 30 (.leaf (-36)) (.branch 31 (.leaf (-35)) (.leaf (-34)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (-33)) (.leaf (-32))) (.branch 35 (.leaf (-31)) (.branch 36 (.leaf (-30)) (.leaf (-29))))) (.branch 40 (.branch 38 (.leaf (-28)) (.branch 39 (.leaf (-27)) (.leaf (-26)))) (.branch 41 (.leaf (-25)) (.branch 42 (.leaf (-24)) (.leaf (-23))))))) (.branch 54 (.branch 48 (.branch 45 (.branch 44 (.leaf (-22)) (.leaf (-21))) (.branch 46 (.leaf (-20)) (.branch 47 (.leaf (-19)) (.leaf (-18))))) (.branch 51 (.branch 49 (.leaf (-17)) (.branch 50 (.leaf (-16)) (.leaf (-15)))) (.branch 52 (.leaf (-14)) (.branch 53 (.leaf (-13)) (.leaf (-12)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-11)) (.leaf (-10))) (.branch 57 (.leaf (-9)) (.branch 58 (.leaf (-8)) (.leaf (-7))))) (.branch 62 (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-5)) (.leaf (-4)))) (.branch 63 (.leaf (-3)) (.branch 64 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.leaf (-31)) (.branch 36 (.leaf (-30)) (.leaf (-29)))) (.branch 39 (.branch 38 (.leaf (-28)) (.leaf (-27))) (.branch 40 (.leaf (-26)) (.leaf (-25))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-24)) (.leaf (-23))) (.branch 44 (.leaf (-22)) (.leaf (-21)))) (.branch 47 (.branch 46 (.leaf (-20)) (.leaf (-19))) (.branch 48 (.leaf (-18)) (.leaf (-17)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (-16)) (.leaf (-15))) (.branch 52 (.leaf (-14)) (.leaf (-13)))) (.branch 55 (.branch 54 (.leaf (-12)) (.leaf (-11))) (.branch 56 (.leaf (-10)) (.leaf (-9))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-8)) (.leaf (-7))) (.branch 60 (.leaf (-6)) (.leaf (-5)))) (.branch 63 (.branch 62 (.leaf (-4)) (.leaf (-3))) (.branch 64 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 51 (.branch 49 (.branch 48 (.leaf (-18)) (.leaf (-17))) (.branch 50 (.leaf (-16)) (.leaf (-15)))) (.branch 53 (.branch 52 (.leaf (-14)) (.leaf (-13))) (.branch 54 (.leaf (-12)) (.branch 55 (.leaf (-11)) (.leaf (-10)))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-9)) (.leaf (-8))) (.branch 59 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.branch 61 (.leaf (-5)) (.leaf (-4))) (.branch 63 (.leaf (-3)) (.branch 64 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 62 (.branch 61 (.leaf (-5)) (.leaf (-4))) (.branch 63 (.leaf (-3)) (.branch 64 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_290_4983 : CycleWitness 9 where
  length := 65
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (8))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (5))) (.branch 31 (.leaf (1)) (.leaf (0))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (3)) (.leaf (0))) (.branch 35 (.leaf (6)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (7)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (8)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (3))) (.branch 47 (.leaf (0)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (5)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (6))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (3)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (7)) (.leaf (1))) (.branch 63 (.leaf (0)) (.branch 64 (.leaf (2)) (.leaf (8)))))))))
  code := certificateP9_4983
  counts := ![(.branch 32 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 27 (.branch 24 (.leaf (9)) (.leaf (10))) (.branch 29 (.leaf (11)) (.leaf (12)))))) (.branch 47 (.branch 40 (.branch 34 (.leaf (13)) (.branch 37 (.leaf (14)) (.leaf (15)))) (.branch 42 (.leaf (16)) (.branch 45 (.leaf (17)) (.leaf (18))))) (.branch 55 (.branch 50 (.leaf (19)) (.branch 53 (.leaf (20)) (.leaf (21)))) (.branch 60 (.branch 58 (.leaf (22)) (.leaf (23))) (.branch 63 (.leaf (24)) (.leaf (25))))))),
  (.branch 31 (.branch 15 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 49 (.branch 41 (.branch 36 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 57 (.branch 54 (.leaf (12)) (.leaf (13))) (.branch 62 (.leaf (14)) (.leaf (15)))))),
  (.branch 38 (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3)))),
  (.branch 43 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-8)))) (.branch 44 (.branch 31 (.leaf (-9)) (.leaf (-10))) (.branch 57 (.leaf (-11)) (.leaf (-12))))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-53))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (-38)) (.leaf (-40)))),
  (.branch 13 (.leaf (0)) (.branch 56 (.leaf (-26)) (.leaf (-27)))),
  (.branch 17 (.leaf (0)) (.leaf (-14))),
  (.branch 43 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 61 (.leaf (-12)) (.branch 64 (.leaf (-10)) (.leaf (-5)))),
  (.branch 63 (.branch 58 (.leaf (-12)) (.leaf (-11))) (.branch 64 (.leaf (-9)) (.leaf (-7)))),
  (.leaf (-1)),
  (.branch 62 (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-5)) (.leaf (-4)))) (.branch 63 (.leaf (-3)) (.branch 64 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 50 (.branch 27 (.branch 5 (.leaf (-53)) (.leaf (-52))) (.branch 49 (.leaf (-51)) (.leaf (-48)))) (.branch 52 (.branch 51 (.leaf (-45)) (.leaf (-42))) (.branch 53 (.leaf (-39)) (.branch 54 (.leaf (-36)) (.leaf (-33)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-30)) (.leaf (-27))) (.branch 58 (.leaf (-24)) (.branch 59 (.leaf (-21)) (.leaf (-18))))) (.branch 62 (.branch 61 (.leaf (-15)) (.leaf (-12))) (.branch 63 (.leaf (-9)) (.branch 64 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 58 (.branch 54 (.branch 31 (.leaf (-40)) (.branch 53 (.leaf (-39)) (.leaf (-36)))) (.branch 56 (.branch 55 (.leaf (-33)) (.leaf (-30))) (.branch 57 (.leaf (-27)) (.leaf (-24))))) (.branch 61 (.branch 59 (.leaf (-21)) (.branch 60 (.leaf (-18)) (.leaf (-15)))) (.branch 63 (.branch 62 (.leaf (-12)) (.leaf (-9))) (.branch 64 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-27)) (.leaf (-24))) (.branch 59 (.leaf (-21)) (.leaf (-18)))) (.branch 62 (.branch 61 (.leaf (-15)) (.leaf (-12))) (.branch 63 (.leaf (-9)) (.branch 64 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 62 (.branch 18 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 63 (.leaf (-9)) (.branch 64 (.leaf (-6)) (.leaf (-3))))),
  (.branch 44 (.leaf (-1)) (.leaf (0)))]
def witnessP9_290_4984 : CycleWitness 9 where
  length := 65
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (8))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (0))) (.branch 19 (.leaf (3)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (5))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (7)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (3)) (.leaf (0))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (2)) (.leaf (4))) (.branch 35 (.leaf (0)) (.leaf (8)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (5)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (3))) (.branch 43 (.leaf (0)) (.leaf (6)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (7)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (5)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (8))) (.branch 59 (.leaf (1)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (6)) (.leaf (4))) (.branch 63 (.leaf (0)) (.branch 64 (.leaf (2)) (.leaf (3)))))))))
  code := certificateP9_4984
  counts := ![(.branch 32 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 27 (.leaf (9)) (.branch 29 (.leaf (10)) (.leaf (11)))))) (.branch 49 (.branch 40 (.branch 35 (.leaf (12)) (.branch 37 (.leaf (13)) (.leaf (14)))) (.branch 43 (.leaf (15)) (.branch 46 (.leaf (16)) (.leaf (17))))) (.branch 57 (.branch 51 (.leaf (18)) (.branch 54 (.leaf (19)) (.leaf (20)))) (.branch 60 (.leaf (21)) (.branch 63 (.leaf (22)) (.leaf (23))))))),
  (.branch 30 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 59 (.leaf (8)) (.leaf (9)))))),
  (.branch 33 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 11 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 62 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 37 (.leaf (-22)) (.branch 51 (.leaf (-26)) (.leaf (-29))))),
  (.branch 23 (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-13)))) (.branch 52 (.branch 30 (.leaf (-14)) (.leaf (-15))) (.branch 59 (.leaf (-16)) (.leaf (-17))))),
  (.branch 41 (.branch 8 (.leaf (0)) (.branch 33 (.leaf (-2)) (.leaf (-5)))) (.branch 56 (.leaf (-7)) (.branch 64 (.leaf (-14)) (.leaf (-16))))),
  (.branch 11 (.leaf (0)) (.branch 19 (.leaf (-1)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (-20)) (.leaf (-22)))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (-7))) (.branch 44 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (-53)) (.leaf (-55)))),
  (.branch 14 (.leaf (0)) (.leaf (-23)))]
  high := ![(.branch 58 (.branch 52 (.leaf (-29)) (.branch 55 (.leaf (-28)) (.leaf (-27)))) (.branch 61 (.leaf (-26)) (.branch 64 (.leaf (-25)) (.leaf (-17))))),
  (.branch 62 (.branch 60 (.leaf (-17)) (.branch 61 (.leaf (-15)) (.leaf (-13)))) (.branch 63 (.leaf (-11)) (.branch 64 (.leaf (-9)) (.leaf (-7))))),
  (.leaf (-16)),
  (.branch 55 (.branch 20 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-9)))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-1)) (.leaf (0))))),
  (.branch 49 (.branch 21 (.leaf (-22)) (.branch 35 (.leaf (-21)) (.leaf (-20)))) (.branch 63 (.leaf (-19)) (.branch 64 (.leaf (-16)) (.leaf (-13))))),
  (.branch 59 (.branch 56 (.branch 6 (.leaf (-23)) (.leaf (-22))) (.branch 57 (.leaf (-20)) (.branch 58 (.leaf (-18)) (.leaf (-16))))) (.branch 62 (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 63 (.leaf (-8)) (.branch 64 (.leaf (-6)) (.leaf (-4)))))),
  (.branch 62 (.branch 45 (.leaf (-11)) (.leaf (-10))) (.branch 63 (.leaf (-8)) (.branch 64 (.leaf (-6)) (.leaf (-4))))),
  (.branch 55 (.branch 50 (.branch 48 (.branch 26 (.leaf (-55)) (.leaf (-54))) (.branch 49 (.leaf (-51)) (.leaf (-48)))) (.branch 52 (.branch 51 (.leaf (-45)) (.leaf (-42))) (.branch 53 (.leaf (-39)) (.branch 54 (.leaf (-36)) (.leaf (-33)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-30)) (.leaf (-27))) (.branch 58 (.leaf (-24)) (.branch 59 (.leaf (-21)) (.leaf (-18))))) (.branch 62 (.branch 61 (.leaf (-15)) (.leaf (-12))) (.branch 63 (.leaf (-9)) (.branch 64 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 60 (.branch 37 (.branch 15 (.leaf (-23)) (.leaf (-22))) (.branch 59 (.leaf (-21)) (.leaf (-18)))) (.branch 62 (.branch 61 (.leaf (-15)) (.leaf (-12))) (.branch 63 (.leaf (-9)) (.branch 64 (.leaf (-6)) (.leaf (-3))))))]
def witnessP9_290 : Fin 45 → CycleWitness 9 := ![witnessP9_290_4940, witnessP9_290_4941, witnessP9_290_4942, witnessP9_290_4943, witnessP9_290_4944, witnessP9_290_4945, witnessP9_290_4946, witnessP9_290_4947, witnessP9_290_4948, witnessP9_290_4949, witnessP9_290_4950, witnessP9_290_4951, witnessP9_290_4952, witnessP9_290_4953, witnessP9_290_4954, witnessP9_290_4955, witnessP9_290_4956, witnessP9_290_4957, witnessP9_290_4958, witnessP9_290_4959, witnessP9_290_4960, witnessP9_290_4961, witnessP9_290_4962, witnessP9_290_4963, witnessP9_290_4964, witnessP9_290_4965, witnessP9_290_4966, witnessP9_290_4967, witnessP9_290_4968, witnessP9_290_4969, witnessP9_290_4970, witnessP9_290_4971, witnessP9_290_4972, witnessP9_290_4973, witnessP9_290_4974, witnessP9_290_4975, witnessP9_290_4976, witnessP9_290_4977, witnessP9_290_4978, witnessP9_290_4979, witnessP9_290_4980, witnessP9_290_4981, witnessP9_290_4982, witnessP9_290_4983, witnessP9_290_4984]
end RealPinwheel.FiveSixths


