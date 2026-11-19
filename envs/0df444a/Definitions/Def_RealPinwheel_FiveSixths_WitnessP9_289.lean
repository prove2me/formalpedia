-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_289
-- name    : RealPinwheel_FiveSixths_WitnessP9_289
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:20:28.665978+00:00
-- url     : https://prove2.me/theorems/009ec0e7-1cd0-4694-a9a7-125486ec5e86
-- title:
--   Exact witness block P9_289
-- statement:
--   These exact witnesses represent words 4896 through 4940 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 4896–4940; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_289_4895 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (2))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (5)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (4)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (5))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (4))) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (5)) (.leaf (4)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (3)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (8)) (.leaf (0))) (.branch 41 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (2)) (.leaf (3))) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (4)) (.leaf (2))) (.branch 49 (.leaf (1)) (.branch 50 (.leaf (5)) (.leaf (3))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (2))) (.branch 54 (.leaf (4)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (6)) (.leaf (0))) (.branch 58 (.leaf (3)) (.leaf (5))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (2)) (.leaf (4))) (.branch 62 (.leaf (1)) (.leaf (0)))) (.branch 65 (.branch 64 (.leaf (3)) (.leaf (2))) (.branch 66 (.leaf (1)) (.branch 67 (.leaf (5)) (.leaf (4)))))))))
  code := certificateP9_4895
  counts := ![(.branch 29 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 15 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 38 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 34 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 41 (.leaf (5)) (.branch 47 (.leaf (6)) (.leaf (7)))) (.branch 61 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 67 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.leaf (0)) (.branch 56 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-14)) (.leaf (-16)))),
  (.branch 32 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))) (.branch 49 (.leaf (-4)) (.branch 66 (.leaf (-5)) (.leaf (-6))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 36 (.leaf (-5)) (.branch 53 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 30 (.leaf (-19)) (.leaf (-20)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 22 (.leaf (0)) (.leaf (-12))),
  (.branch 5 (.leaf (0)) (.leaf (-63))),
  (.branch 39 (.leaf (0)) (.leaf (-29)))]
  high := ![(.branch 65 (.branch 58 (.leaf (-16)) (.branch 64 (.leaf (-15)) (.leaf (-12)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 67 (.leaf (-6)) (.leaf (-5))),
  (.branch 66 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5)))),
  (.branch 66 (.branch 65 (.leaf (-20)) (.leaf (-15))) (.branch 67 (.leaf (-10)) (.leaf (-5)))),
  (.branch 55 (.branch 48 (.leaf (-3)) (.leaf (-2))) (.branch 62 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-2)),
  (.branch 62 (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-11)) (.leaf (-10)))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 20 (.branch 12 (.branch 8 (.branch 6 (.leaf (-63)) (.branch 7 (.leaf (-62)) (.leaf (-61)))) (.branch 10 (.branch 9 (.leaf (-60)) (.leaf (-59))) (.branch 11 (.leaf (-58)) (.leaf (-57))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-56)) (.leaf (-55))) (.branch 15 (.leaf (-54)) (.leaf (-53)))) (.branch 18 (.branch 17 (.leaf (-52)) (.leaf (-51))) (.branch 19 (.leaf (-50)) (.leaf (-49)))))) (.branch 28 (.branch 24 (.branch 22 (.branch 21 (.leaf (-48)) (.leaf (-47))) (.branch 23 (.leaf (-46)) (.leaf (-45)))) (.branch 26 (.branch 25 (.leaf (-44)) (.leaf (-43))) (.branch 27 (.leaf (-42)) (.leaf (-41))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-40)) (.leaf (-39))) (.branch 31 (.leaf (-38)) (.leaf (-37)))) (.branch 34 (.branch 33 (.leaf (-36)) (.leaf (-35))) (.branch 35 (.leaf (-34)) (.leaf (-33))))))) (.branch 52 (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-32)) (.leaf (-31))) (.branch 39 (.leaf (-30)) (.leaf (-29)))) (.branch 42 (.branch 41 (.leaf (-28)) (.leaf (-27))) (.branch 43 (.leaf (-26)) (.leaf (-25))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-24)) (.leaf (-23))) (.branch 47 (.leaf (-22)) (.leaf (-21)))) (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-19))) (.branch 51 (.leaf (-18)) (.leaf (-17)))))) (.branch 60 (.branch 56 (.branch 54 (.branch 53 (.leaf (-16)) (.leaf (-15))) (.branch 55 (.leaf (-14)) (.leaf (-13)))) (.branch 58 (.branch 57 (.leaf (-12)) (.leaf (-11))) (.branch 59 (.leaf (-10)) (.leaf (-9))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 53 (.branch 46 (.branch 42 (.branch 40 (.leaf (-29)) (.branch 41 (.leaf (-28)) (.leaf (-27)))) (.branch 44 (.branch 43 (.leaf (-26)) (.leaf (-25))) (.branch 45 (.leaf (-24)) (.leaf (-23))))) (.branch 49 (.branch 47 (.leaf (-22)) (.branch 48 (.leaf (-21)) (.leaf (-20)))) (.branch 51 (.branch 50 (.leaf (-19)) (.leaf (-18))) (.branch 52 (.leaf (-17)) (.leaf (-16)))))) (.branch 60 (.branch 56 (.branch 54 (.leaf (-15)) (.branch 55 (.leaf (-14)) (.leaf (-13)))) (.branch 58 (.branch 57 (.leaf (-12)) (.leaf (-11))) (.branch 59 (.leaf (-10)) (.leaf (-9))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_289_4896 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (5))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (6))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (2))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (3)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (3)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (5))) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (7))) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (4)) (.leaf (2))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (3)) (.leaf (1)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (3)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (5))) (.branch 41 (.leaf (0)) (.leaf (2))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (3)) (.leaf (6))) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (4)) (.leaf (2))) (.branch 49 (.leaf (5)) (.branch 50 (.leaf (3)) (.leaf (1))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (2))) (.branch 54 (.leaf (3)) (.leaf (4)))) (.branch 57 (.branch 56 (.leaf (1)) (.leaf (5))) (.branch 58 (.leaf (0)) (.leaf (2))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (3)) (.leaf (8))) (.branch 62 (.leaf (1)) (.leaf (0)))) (.branch 65 (.branch 64 (.leaf (4)) (.leaf (2))) (.branch 66 (.leaf (5)) (.branch 67 (.leaf (3)) (.leaf (1)))))))))
  code := certificateP9_4896
  counts := ![(.branch 29 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 67 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 61 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 37 (.leaf (-4)) (.branch 54 (.leaf (-5)) (.leaf (-6))))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-24))),
  (.branch 27 (.leaf (0)) (.leaf (-41))),
  (.branch 61 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-12))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.leaf (-2)) (.branch 63 (.leaf (-1)) (.leaf (0)))),
  (.branch 60 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.leaf (-6)) (.leaf (-5))),
  (.branch 65 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 58 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-2)))),
  (.branch 56 (.branch 50 (.branch 47 (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-23)) (.leaf (-22)))) (.branch 48 (.leaf (-21)) (.branch 49 (.leaf (-20)) (.leaf (-19))))) (.branch 53 (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-17)) (.leaf (-16)))) (.branch 54 (.leaf (-15)) (.branch 55 (.leaf (-14)) (.leaf (-13)))))) (.branch 62 (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-11)) (.leaf (-10)))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 47 (.branch 37 (.branch 32 (.branch 29 (.branch 28 (.leaf (-41)) (.leaf (-40))) (.branch 30 (.leaf (-39)) (.branch 31 (.leaf (-38)) (.leaf (-37))))) (.branch 34 (.branch 33 (.leaf (-36)) (.leaf (-35))) (.branch 35 (.leaf (-34)) (.branch 36 (.leaf (-33)) (.leaf (-32)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (-31)) (.leaf (-30))) (.branch 40 (.leaf (-29)) (.branch 41 (.leaf (-28)) (.leaf (-27))))) (.branch 44 (.branch 43 (.leaf (-26)) (.leaf (-25))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-23)) (.leaf (-22))))))) (.branch 57 (.branch 52 (.branch 49 (.branch 48 (.leaf (-21)) (.leaf (-20))) (.branch 50 (.leaf (-19)) (.branch 51 (.leaf (-18)) (.leaf (-17))))) (.branch 54 (.branch 53 (.leaf (-16)) (.leaf (-15))) (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))))) (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_289_4897 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (2))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (4)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (6)) (.leaf (4))) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (2))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (1)) (.leaf (4)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (3)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (4))) (.branch 41 (.leaf (0)) (.leaf (2))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (8)) (.leaf (3))) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (4)) (.leaf (2))) (.branch 49 (.leaf (5)) (.branch 50 (.leaf (1)) (.leaf (3))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (2))) (.branch 54 (.leaf (4)) (.leaf (5)))) (.branch 57 (.branch 56 (.leaf (1)) (.leaf (3))) (.branch 58 (.leaf (0)) (.leaf (2))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (6)) (.leaf (4))) (.branch 62 (.leaf (1)) (.leaf (0)))) (.branch 65 (.branch 64 (.leaf (3)) (.leaf (2))) (.branch 66 (.leaf (5)) (.branch 67 (.leaf (1)) (.leaf (4)))))))))
  code := certificateP9_4897
  counts := ![(.branch 29 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 67 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 34 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 40 (.leaf (5)) (.branch 47 (.leaf (6)) (.leaf (7)))) (.branch 61 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.leaf (0)) (.branch 60 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-19)) (.leaf (-21)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (-6))) (.branch 38 (.leaf (-9)) (.branch 55 (.leaf (-12)) (.leaf (-15))))),
  (.branch 26 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-59))),
  (.branch 43 (.leaf (0)) (.leaf (-25)))]
  high := ![(.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-12))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 60 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 65 (.branch 58 (.leaf (-21)) (.leaf (-20))) (.branch 66 (.leaf (-15)) (.branch 67 (.leaf (-10)) (.leaf (-5))))),
  (.branch 48 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.branch 62 (.leaf (-1)) (.leaf (0))))),
  (.branch 56 (.leaf (-15)) (.branch 67 (.leaf (-14)) (.leaf (-13)))),
  (.branch 64 (.branch 62 (.branch 61 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.branch 23 (.branch 16 (.branch 12 (.branch 10 (.leaf (-59)) (.branch 11 (.leaf (-58)) (.leaf (-57)))) (.branch 14 (.branch 13 (.leaf (-56)) (.leaf (-55))) (.branch 15 (.leaf (-54)) (.leaf (-53))))) (.branch 19 (.branch 17 (.leaf (-52)) (.branch 18 (.leaf (-51)) (.leaf (-50)))) (.branch 21 (.branch 20 (.leaf (-49)) (.leaf (-48))) (.branch 22 (.leaf (-47)) (.leaf (-46)))))) (.branch 30 (.branch 26 (.branch 24 (.leaf (-45)) (.branch 25 (.leaf (-44)) (.leaf (-43)))) (.branch 28 (.branch 27 (.leaf (-42)) (.leaf (-41))) (.branch 29 (.leaf (-40)) (.leaf (-39))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-38)) (.leaf (-37))) (.branch 33 (.leaf (-36)) (.leaf (-35)))) (.branch 36 (.branch 35 (.leaf (-34)) (.leaf (-33))) (.branch 37 (.leaf (-32)) (.leaf (-31))))))) (.branch 53 (.branch 45 (.branch 41 (.branch 39 (.leaf (-30)) (.branch 40 (.leaf (-29)) (.leaf (-28)))) (.branch 43 (.branch 42 (.leaf (-27)) (.leaf (-26))) (.branch 44 (.leaf (-25)) (.leaf (-24))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (-23)) (.leaf (-22))) (.branch 48 (.leaf (-21)) (.leaf (-20)))) (.branch 51 (.branch 50 (.leaf (-19)) (.leaf (-18))) (.branch 52 (.leaf (-17)) (.leaf (-16)))))) (.branch 60 (.branch 56 (.branch 54 (.leaf (-15)) (.branch 55 (.leaf (-14)) (.leaf (-13)))) (.branch 58 (.branch 57 (.leaf (-12)) (.leaf (-11))) (.branch 59 (.leaf (-10)) (.leaf (-9))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 55 (.branch 49 (.branch 46 (.branch 44 (.leaf (-25)) (.branch 45 (.leaf (-24)) (.leaf (-23)))) (.branch 47 (.leaf (-22)) (.branch 48 (.leaf (-21)) (.leaf (-20))))) (.branch 52 (.branch 50 (.leaf (-19)) (.branch 51 (.leaf (-18)) (.leaf (-17)))) (.branch 53 (.leaf (-16)) (.branch 54 (.leaf (-15)) (.leaf (-14)))))) (.branch 61 (.branch 58 (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))) (.branch 59 (.leaf (-10)) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_289_4898 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (7)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (4))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (5)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (8)) (.leaf (6))) (.branch 24 (.leaf (0)) (.leaf (4))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (5))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (7)) (.leaf (1)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (4)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (3)) (.leaf (6))) (.branch 41 (.leaf (0)) (.leaf (5))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (1)) (.leaf (0))) (.branch 45 (.leaf (8)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (4))) (.branch 49 (.leaf (0)) (.branch 50 (.leaf (3)) (.leaf (1))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (2))) (.branch 54 (.leaf (5)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (7)) (.leaf (6))) (.branch 58 (.leaf (0)) (.leaf (4))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (1)) (.leaf (0))) (.branch 62 (.leaf (3)) (.leaf (2)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (5))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (8)) (.leaf (1)))))))))
  code := certificateP9_4898
  counts := ![(.branch 32 (.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 27 (.leaf (9)) (.branch 30 (.leaf (10)) (.leaf (11)))))) (.branch 49 (.branch 41 (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14)))) (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17))))) (.branch 58 (.branch 52 (.leaf (18)) (.branch 55 (.leaf (19)) (.leaf (20)))) (.branch 64 (.branch 61 (.leaf (21)) (.leaf (22))) (.branch 66 (.leaf (23)) (.leaf (24))))))),
  (.branch 34 (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 45 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 67 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 36 (.leaf (-8)) (.branch 53 (.leaf (-9)) (.leaf (-10))))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-19)) (.leaf (-20)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-25))) (.branch 25 (.leaf (-26)) (.leaf (-27)))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.branch 33 (.leaf (-35)) (.leaf (-37)))),
  (.branch 22 (.leaf (0)) (.branch 67 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 67 (.leaf (-12)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 65 (.branch 54 (.leaf (-10)) (.branch 64 (.leaf (-9)) (.leaf (-8)))) (.branch 66 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5))))),
  (.branch 64 (.branch 51 (.leaf (-20)) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-27)) (.leaf (-24))) (.branch 62 (.leaf (-21)) (.leaf (-18)))) (.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-12))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 66 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 61 (.branch 58 (.branch 34 (.leaf (-37)) (.branch 57 (.leaf (-36)) (.leaf (-33)))) (.branch 59 (.leaf (-30)) (.branch 60 (.leaf (-27)) (.leaf (-24))))) (.branch 64 (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (-3))]
def witnessP9_289_4899 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (6)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (7))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (0)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (2))) (.branch 20 (.leaf (8)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (1))) (.branch 24 (.leaf (6)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (5))) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (7)) (.branch 33 (.leaf (1)) (.leaf (3)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (5)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (4)) (.leaf (0))) (.branch 41 (.leaf (6)) (.leaf (2))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (1)) (.leaf (8))) (.branch 45 (.leaf (0)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (2))) (.branch 49 (.leaf (5)) (.branch 50 (.leaf (0)) (.leaf (4))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (1)) (.leaf (2))) (.branch 54 (.leaf (7)) (.leaf (0)))) (.branch 57 (.branch 56 (.leaf (3)) (.leaf (1))) (.branch 58 (.leaf (6)) (.leaf (2))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (0)) (.leaf (5))) (.branch 62 (.leaf (1)) (.leaf (4)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (2))) (.branch 66 (.leaf (8)) (.branch 67 (.leaf (1)) (.leaf (3)))))))))
  code := certificateP9_4899
  counts := ![(.branch 30 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 50 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 60 (.branch 55 (.leaf (11)) (.leaf (12))) (.branch 64 (.leaf (13)) (.leaf (14)))))),
  (.branch 33 (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))) (.branch 52 (.branch 43 (.branch 38 (.leaf (7)) (.leaf (8))) (.branch 47 (.leaf (9)) (.leaf (10)))) (.branch 62 (.branch 57 (.leaf (11)) (.leaf (12))) (.branch 67 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 12 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 30 (.leaf (-27)) (.leaf (-28)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-6)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 22 (.leaf (0)) (.branch 56 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 39 (.leaf (-13)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.branch 37 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 32 (.branch 10 (.leaf (0)) (.leaf (-13))) (.branch 54 (.leaf (-14)) (.leaf (-15)))),
  (.branch 20 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 66 (.branch 65 (.leaf (-28)) (.leaf (-21))) (.branch 67 (.leaf (-14)) (.leaf (-7)))),
  (.branch 53 (.branch 48 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 63 (.leaf (-8)) (.leaf (-7))))),
  (.branch 60 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.leaf (-3)) (.branch 58 (.leaf (-1)) (.leaf (0)))),
  (.branch 64 (.branch 40 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 66 (.branch 65 (.leaf (-10)) (.leaf (-8))) (.branch 67 (.leaf (-6)) (.leaf (-4))))),
  (.branch 63 (.branch 50 (.branch 38 (.leaf (-18)) (.leaf (-17))) (.branch 62 (.leaf (-16)) (.leaf (-14)))) (.branch 65 (.branch 64 (.leaf (-12)) (.leaf (-10))) (.branch 66 (.leaf (-8)) (.branch 67 (.leaf (-6)) (.leaf (-4)))))),
  (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 61 (.branch 57 (.branch 55 (.leaf (-15)) (.branch 56 (.leaf (-14)) (.leaf (-13)))) (.branch 59 (.branch 58 (.leaf (-12)) (.leaf (-11))) (.branch 60 (.leaf (-10)) (.leaf (-9))))) (.branch 64 (.branch 62 (.leaf (-8)) (.branch 63 (.leaf (-7)) (.leaf (-6)))) (.branch 66 (.branch 65 (.leaf (-5)) (.leaf (-4))) (.branch 67 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 67 (.leaf (-3)) (.leaf (-2)))]
def witnessP9_289_4900 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (6))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (5))) (.branch 15 (.leaf (8)) (.branch 16 (.leaf (2)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (4)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (7)) (.leaf (3))) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (4))) (.branch 32 (.leaf (8)) (.branch 33 (.leaf (6)) (.leaf (1)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (5)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (7))) (.branch 41 (.leaf (0)) (.leaf (4))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (2)) (.leaf (3))) (.branch 45 (.leaf (1)) (.leaf (6)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (5))) (.branch 49 (.leaf (8)) (.branch 50 (.leaf (2)) (.leaf (1))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (7))) (.branch 54 (.leaf (4)) (.leaf (3)))) (.branch 57 (.branch 56 (.leaf (1)) (.leaf (2))) (.branch 58 (.leaf (0)) (.leaf (5))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (6)) (.leaf (3))) (.branch 62 (.leaf (1)) (.leaf (2)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (4))) (.branch 66 (.leaf (8)) (.branch 67 (.leaf (7)) (.leaf (1)))))))))
  code := certificateP9_4900
  counts := ![(.branch 30 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 36 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 40 (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 53 (.leaf (3)) (.branch 67 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 29 (.leaf (-24)) (.leaf (-25)))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-6)) (.leaf (-10)))) (.branch 44 (.leaf (-13)) (.branch 61 (.leaf (-16)) (.leaf (-19))))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-25))) (.branch 25 (.leaf (-26)) (.leaf (-27)))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (-38))) (.branch 46 (.leaf (-41)) (.leaf (-42)))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.branch 15 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 65 (.branch 53 (.leaf (-14)) (.branch 59 (.leaf (-13)) (.leaf (-12)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.leaf (-2)) (.branch 63 (.leaf (-1)) (.leaf (0)))),
  (.branch 65 (.branch 64 (.leaf (-25)) (.leaf (-20))) (.branch 66 (.leaf (-15)) (.branch 67 (.leaf (-10)) (.leaf (-5))))),
  (.branch 64 (.branch 62 (.leaf (-19)) (.branch 63 (.leaf (-18)) (.leaf (-17)))) (.branch 66 (.branch 65 (.leaf (-16)) (.leaf (-15))) (.branch 67 (.leaf (-14)) (.leaf (-13))))),
  (.branch 66 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3)))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-27)) (.leaf (-24))) (.branch 62 (.leaf (-21)) (.leaf (-18)))) (.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-12))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 63 (.branch 61 (.branch 47 (.leaf (-42)) (.leaf (-40))) (.branch 62 (.leaf (-35)) (.leaf (-30)))) (.branch 65 (.branch 64 (.leaf (-25)) (.leaf (-20))) (.branch 66 (.leaf (-15)) (.branch 67 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 13 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-5)))),
  (.branch 67 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_289_4901 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (7)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (8)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (6))) (.branch 11 (.leaf (2)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (7))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (5))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (8)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (7)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (8)))) (.branch 31 (.branch 30 (.leaf (4)) (.leaf (0))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (6)) (.leaf (5)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (1)) (.leaf (2))) (.branch 37 (.leaf (7)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (3))) (.branch 41 (.leaf (8)) (.leaf (5))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (1)) (.leaf (6))) (.branch 45 (.leaf (2)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (4)) (.leaf (7))) (.branch 49 (.leaf (3)) (.branch 50 (.leaf (1)) (.leaf (5))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (8)) (.leaf (2))) (.branch 54 (.leaf (0)) (.leaf (4)))) (.branch 57 (.branch 56 (.leaf (6)) (.leaf (3))) (.branch 58 (.leaf (1)) (.leaf (5))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (7)) (.leaf (0))) (.branch 62 (.leaf (2)) (.leaf (8)))) (.branch 65 (.branch 64 (.leaf (4)) (.leaf (1))) (.branch 66 (.leaf (3)) (.branch 67 (.leaf (6)) (.leaf (5)))))))))
  code := certificateP9_4901
  counts := ![(.branch 31 (.branch 9 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 54 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 67 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 31 (.branch 1 (.leaf (0)) (.branch 16 (.leaf (-59)) (.leaf (-60)))) (.branch 46 (.leaf (-61)) (.branch 61 (.leaf (-62)) (.leaf (-63))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-23))) (.branch 27 (.leaf (-28)) (.leaf (-29)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-25)) (.leaf (-26)))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (-13))) (.branch 29 (.leaf (-14)) (.leaf (-15))))]
  high := ![(.branch 64 (.branch 62 (.leaf (-63)) (.branch 63 (.leaf (-54)) (.leaf (-45)))) (.branch 66 (.branch 65 (.leaf (-36)) (.leaf (-27))) (.branch 67 (.leaf (-18)) (.leaf (-9))))),
  (.branch 66 (.branch 28 (.leaf (-29)) (.leaf (-27))) (.branch 67 (.leaf (-18)) (.leaf (-9)))),
  (.branch 64 (.branch 54 (.leaf (-13)) (.branch 63 (.leaf (-12)) (.leaf (-10)))) (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-6))) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 58 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-2)))),
  (.branch 65 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 60 (.leaf (-1)) (.leaf (0))),
  (.branch 45 (.leaf (-4)) (.leaf (-3))),
  (.branch 63 (.branch 61 (.branch 49 (.leaf (-26)) (.leaf (-24))) (.branch 62 (.leaf (-21)) (.leaf (-18)))) (.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-12))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-12))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_289_4902 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (7)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (1)) (.leaf (8))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (7)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (4)) (.leaf (3))) (.branch 28 (.leaf (1)) (.leaf (6)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (3)) (.leaf (8)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (1)) (.leaf (2))) (.branch 37 (.leaf (0)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (3)) (.leaf (1))) (.branch 41 (.leaf (7)) (.leaf (2))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (5)) (.leaf (0))) (.branch 45 (.leaf (3)) (.leaf (6)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (2))) (.branch 49 (.leaf (4)) (.branch 50 (.leaf (0)) (.leaf (8))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (3)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (5)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (3))) (.branch 58 (.leaf (7)) (.leaf (1))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (4)) (.leaf (2))) (.branch 62 (.leaf (0)) (.leaf (6)))) (.branch 65 (.branch 64 (.leaf (3)) (.leaf (1))) (.branch 66 (.leaf (5)) (.branch 67 (.leaf (2)) (.leaf (8)))))))))
  code := certificateP9_4902
  counts := ![(.branch 31 (.branch 13 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 37 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 56 (.leaf (9)) (.branch 62 (.leaf (10)) (.leaf (11)))))),
  (.branch 35 (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 53 (.branch 40 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))) (.branch 59 (.leaf (9)) (.branch 65 (.leaf (10)) (.leaf (11)))))),
  (.branch 36 (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))) (.branch 54 (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))) (.branch 61 (.leaf (9)) (.branch 67 (.leaf (10)) (.leaf (11)))))),
  (.branch 33 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 52 (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 57 (.leaf (9)) (.branch 64 (.leaf (10)) (.leaf (11)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.branch 68 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-26)) (.leaf (-32)))),
  (.branch 3 (.leaf (0)) (.branch 40 (.leaf (-16)) (.leaf (-17)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-6))) (.branch 23 (.leaf (-7)) (.leaf (-9)))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-21)) (.leaf (-22)))) (.branch 20 (.leaf (-23)) (.branch 57 (.leaf (-24)) (.leaf (-25))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-22))) (.branch 26 (.leaf (-23)) (.leaf (-24)))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 64 (.branch 38 (.leaf (-32)) (.branch 63 (.leaf (-31)) (.leaf (-26)))) (.branch 66 (.branch 65 (.leaf (-21)) (.leaf (-16))) (.branch 67 (.leaf (-11)) (.leaf (-6))))),
  (.branch 66 (.branch 41 (.leaf (-17)) (.leaf (-16))) (.branch 67 (.leaf (-11)) (.leaf (-6)))),
  (.branch 55 (.leaf (-9)) (.leaf (-6))),
  (.branch 65 (.branch 58 (.leaf (-25)) (.leaf (-21))) (.branch 66 (.leaf (-16)) (.branch 67 (.leaf (-11)) (.leaf (-6))))),
  (.branch 64 (.branch 62 (.branch 61 (.leaf (-24)) (.leaf (-21))) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 44 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-3)))),
  (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))),
  (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_289_4903 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (8)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (1)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (4)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (5)) (.leaf (3))) (.branch 28 (.leaf (1)) (.leaf (7)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (6)) (.branch 33 (.leaf (3)) (.leaf (4)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (1)) (.leaf (2))) (.branch 37 (.leaf (0)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (3)) (.leaf (1))) (.branch 41 (.leaf (4)) (.leaf (2))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (6)) (.leaf (0))) (.branch 45 (.leaf (3)) (.leaf (8)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (2))) (.branch 49 (.leaf (5)) (.branch 50 (.leaf (0)) (.leaf (4))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (3)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (6)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (3))) (.branch 58 (.leaf (4)) (.leaf (1))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (5)) (.leaf (2))) (.branch 62 (.leaf (0)) (.leaf (7)))) (.branch 65 (.branch 64 (.leaf (3)) (.leaf (1))) (.branch 66 (.leaf (6)) (.branch 67 (.leaf (2)) (.leaf (4)))))))))
  code := certificateP9_4903
  counts := ![(.branch 31 (.branch 13 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 37 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 56 (.leaf (9)) (.branch 62 (.leaf (10)) (.leaf (11)))))),
  (.branch 35 (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 53 (.branch 40 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))) (.branch 59 (.leaf (9)) (.branch 65 (.leaf (10)) (.leaf (11)))))),
  (.branch 36 (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))) (.branch 54 (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))) (.branch 61 (.leaf (9)) (.branch 67 (.leaf (10)) (.leaf (11)))))),
  (.branch 33 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 52 (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 57 (.leaf (9)) (.branch 64 (.leaf (10)) (.leaf (11)))))),
  (.branch 34 (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.leaf (0)) (.branch 63 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-26)) (.leaf (-32)))),
  (.branch 3 (.leaf (0)) (.branch 40 (.leaf (-16)) (.leaf (-17)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-6))) (.branch 23 (.leaf (-7)) (.leaf (-9)))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-21)) (.leaf (-22)))) (.branch 20 (.leaf (-23)) (.branch 57 (.leaf (-24)) (.leaf (-25))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (-2))) (.branch 41 (.leaf (-3)) (.branch 58 (.leaf (-4)) (.leaf (-5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-22))) (.branch 26 (.leaf (-23)) (.leaf (-24)))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.branch 29 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-22)))]
  high := ![(.branch 64 (.branch 38 (.leaf (-32)) (.branch 63 (.leaf (-31)) (.leaf (-26)))) (.branch 66 (.branch 65 (.leaf (-21)) (.leaf (-16))) (.branch 67 (.leaf (-11)) (.leaf (-6))))),
  (.branch 66 (.branch 41 (.leaf (-17)) (.leaf (-16))) (.branch 67 (.leaf (-11)) (.leaf (-6)))),
  (.branch 55 (.leaf (-9)) (.leaf (-6))),
  (.branch 65 (.branch 58 (.leaf (-25)) (.leaf (-21))) (.branch 66 (.leaf (-16)) (.branch 67 (.leaf (-11)) (.leaf (-6))))),
  (.branch 61 (.branch 59 (.leaf (-5)) (.branch 60 (.leaf (-4)) (.leaf (-3)))) (.branch 62 (.leaf (-2)) (.branch 63 (.leaf (-1)) (.leaf (0))))),
  (.branch 64 (.branch 62 (.branch 61 (.leaf (-24)) (.leaf (-21))) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.branch 44 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-3)))),
  (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))),
  (.branch 57 (.branch 51 (.branch 48 (.branch 47 (.leaf (-22)) (.leaf (-21))) (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-19)) (.leaf (-18))))) (.branch 54 (.branch 52 (.leaf (-17)) (.branch 53 (.leaf (-16)) (.leaf (-15)))) (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))))) (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_289_4904 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (8)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (6))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (5))) (.branch 15 (.leaf (8)) (.branch 16 (.leaf (2)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (1)) (.leaf (7)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (5)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (8)) (.leaf (4))) (.branch 28 (.leaf (1)) (.leaf (6)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (3))) (.branch 32 (.leaf (7)) (.branch 33 (.leaf (2)) (.leaf (5)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (4))) (.branch 37 (.leaf (1)) (.leaf (8)))) (.branch 40 (.branch 39 (.leaf (6)) (.leaf (0))) (.branch 41 (.leaf (3)) (.leaf (2))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (7)) (.leaf (5))) (.branch 45 (.leaf (1)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (6))) (.branch 49 (.leaf (8)) (.branch 50 (.leaf (2)) (.leaf (3))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (5))) (.branch 54 (.leaf (1)) (.leaf (7)))) (.branch 57 (.branch 56 (.leaf (4)) (.leaf (0))) (.branch 58 (.leaf (6)) (.leaf (2))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (8)) (.leaf (3))) (.branch 62 (.leaf (1)) (.leaf (5)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (4))) (.branch 66 (.leaf (7)) (.branch 67 (.leaf (2)) (.leaf (6)))))))))
  code := certificateP9_4904
  counts := ![(.branch 30 (.branch 13 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 67 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.leaf (7))))),
  (.branch 36 (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 65 (.leaf (6)) (.leaf (7))))),
  (.branch 34 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.leaf (7))))),
  (.branch 39 (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 58 (.branch 48 (.leaf (4)) (.leaf (5))) (.branch 68 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 23 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))) (.branch 40 (.leaf (-7)) (.branch 57 (.leaf (-8)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.branch 31 (.leaf (-54)) (.leaf (-55)))),
  (.branch 36 (.branch 7 (.leaf (0)) (.leaf (-19))) (.branch 65 (.leaf (-20)) (.leaf (-21)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-33)) (.leaf (-38)))),
  (.branch 19 (.leaf (0)) (.branch 48 (.leaf (-3)) (.leaf (-4)))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-22))) (.branch 26 (.leaf (-23)) (.leaf (-24))))]
  high := ![(.branch 65 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 66 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5))))),
  (.branch 65 (.branch 63 (.leaf (-12)) (.branch 64 (.leaf (-10)) (.leaf (-8)))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 63 (.branch 42 (.branch 32 (.leaf (-55)) (.leaf (-53))) (.branch 52 (.leaf (-51)) (.branch 62 (.leaf (-49)) (.leaf (-42))))) (.branch 65 (.branch 64 (.leaf (-35)) (.leaf (-28))) (.branch 66 (.leaf (-21)) (.branch 67 (.leaf (-14)) (.leaf (-7)))))),
  (.branch 66 (.leaf (-21)) (.branch 67 (.leaf (-14)) (.leaf (-7)))),
  (.branch 64 (.branch 15 (.leaf (-38)) (.branch 54 (.leaf (-37)) (.leaf (-35)))) (.branch 66 (.branch 65 (.leaf (-28)) (.leaf (-21))) (.branch 67 (.leaf (-14)) (.leaf (-7))))),
  (.branch 49 (.leaf (-4)) (.branch 59 (.leaf (-2)) (.leaf (0)))),
  (.branch 44 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-3)))),
  (.branch 64 (.branch 62 (.branch 61 (.leaf (-24)) (.leaf (-21))) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_289_4905 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (3))) (.branch 11 (.leaf (2)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (4))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (2)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (8)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (6))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (5)) (.leaf (3))) (.branch 28 (.leaf (2)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (4))) (.branch 32 (.leaf (7)) (.branch 33 (.leaf (2)) (.leaf (1)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (3))) (.branch 37 (.leaf (5)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (4)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (6))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (8)) (.leaf (3))) (.branch 45 (.leaf (2)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (4))) (.branch 49 (.leaf (5)) (.branch 50 (.leaf (2)) (.leaf (1))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (3))) (.branch 54 (.leaf (7)) (.leaf (2)))) (.branch 57 (.branch 56 (.leaf (4)) (.leaf (1))) (.branch 58 (.leaf (0)) (.leaf (6))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (5)) (.leaf (3))) (.branch 62 (.leaf (2)) (.leaf (1)))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (4))) (.branch 66 (.leaf (8)) (.branch 67 (.leaf (2)) (.leaf (1)))))))))
  code := certificateP9_4905
  counts := ![(.branch 30 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 17 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))) (.branch 63 (.branch 57 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 16 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 38 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 67 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 43 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.leaf (0)),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 38 (.leaf (-3)) (.branch 55 (.leaf (-4)) (.leaf (-5))))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-25))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 9 (.leaf (0)) (.branch 54 (.leaf (-41)) (.leaf (-42)))),
  (.branch 20 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 65 (.branch 53 (.leaf (-14)) (.branch 59 (.leaf (-13)) (.leaf (-12)))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.leaf (-5)),
  (.branch 64 (.branch 62 (.leaf (-14)) (.branch 63 (.leaf (-12)) (.leaf (-10)))) (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-6))) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 66 (.branch 57 (.leaf (-7)) (.leaf (-6))) (.branch 67 (.leaf (-4)) (.leaf (-2)))),
  (.branch 63 (.branch 61 (.branch 38 (.leaf (-25)) (.leaf (-24))) (.branch 62 (.leaf (-21)) (.leaf (-18)))) (.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-12))) (.branch 66 (.leaf (-9)) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-9)) (.leaf (-8))) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 61 (.branch 57 (.branch 55 (.leaf (-42)) (.branch 56 (.leaf (-39)) (.leaf (-36)))) (.branch 59 (.branch 58 (.leaf (-33)) (.leaf (-30))) (.branch 60 (.leaf (-27)) (.leaf (-24))))) (.branch 64 (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-18)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-12)) (.leaf (-9))) (.branch 67 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 44 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 67 (.leaf (-6)) (.leaf (-3))))]
def witnessP9_289_4906 : CycleWitness 9 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (4))) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (1)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (1)) (.leaf (3))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (1)) (.leaf (7)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (1)) (.leaf (3)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (4))) (.branch 37 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (5))) (.branch 41 (.leaf (1)) (.leaf (3))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (4))) (.branch 45 (.leaf (1)) (.leaf (6)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (5)) (.branch 50 (.leaf (1)) (.leaf (3))))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (4))) (.branch 54 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (5))) (.branch 58 (.leaf (1)) (.leaf (3))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (0)) (.leaf (4))) (.branch 62 (.leaf (1)) (.leaf (8)))) (.branch 65 (.branch 64 (.leaf (2)) (.leaf (0))) (.branch 66 (.leaf (5)) (.branch 67 (.leaf (1)) (.leaf (3)))))))))
  code := certificateP9_4906
  counts := ![(.branch 31 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 48 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 33 (.branch 16 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 50 (.branch 41 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 45 (.leaf (10)) (.leaf (11)))) (.branch 58 (.branch 54 (.leaf (12)) (.leaf (13))) (.branch 62 (.leaf (14)) (.branch 67 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 68 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 63 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-22))),
  (.branch 29 (.leaf (0)) (.leaf (-39))),
  (.branch 63 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 66 (.branch 61 (.leaf (-15)) (.leaf (-12))) (.branch 67 (.leaf (-8)) (.leaf (-4)))),
  (.branch 63 (.leaf (-7)) (.leaf (-4))),
  (.branch 65 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 66 (.leaf (-6)) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 60 (.leaf (-1)) (.leaf (0))),
  (.branch 64 (.branch 62 (.leaf (-14)) (.branch 63 (.leaf (-12)) (.leaf (-10)))) (.branch 66 (.branch 65 (.leaf (-8)) (.leaf (-6))) (.branch 67 (.leaf (-4)) (.leaf (-2))))),
  (.branch 58 (.leaf (-5)) (.branch 67 (.leaf (-4)) (.leaf (-2)))),
  (.branch 57 (.branch 51 (.branch 48 (.branch 47 (.leaf (-22)) (.leaf (-21))) (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-19)) (.leaf (-18))))) (.branch 54 (.branch 52 (.leaf (-17)) (.branch 53 (.leaf (-16)) (.leaf (-15)))) (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))))) (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 38 (.branch 33 (.branch 31 (.branch 30 (.leaf (-39)) (.leaf (-38))) (.branch 32 (.leaf (-37)) (.leaf (-36)))) (.branch 35 (.branch 34 (.leaf (-35)) (.leaf (-34))) (.branch 36 (.leaf (-33)) (.branch 37 (.leaf (-32)) (.leaf (-31)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-30)) (.leaf (-29))) (.branch 41 (.leaf (-28)) (.branch 42 (.leaf (-27)) (.leaf (-26))))) (.branch 45 (.branch 44 (.leaf (-25)) (.leaf (-24))) (.branch 46 (.leaf (-23)) (.branch 47 (.leaf (-22)) (.leaf (-21))))))) (.branch 58 (.branch 53 (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-19))) (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-17)) (.leaf (-16))))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-14))) (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))))) (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_289_4907 : CycleWitness 9 where
  length := 67
  word := (.branch 35 (.branch 18 (.branch 10 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 8 (.branch 7 (.leaf (5)) (.leaf (1))) (.branch 9 (.leaf (0)) (.leaf (4))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (7))) (.branch 13 (.leaf (6)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (3)) (.leaf (1)))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (5))) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (0))) (.branch 26 (.leaf (1)) (.leaf (0))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (6)) (.leaf (8))) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (0)) (.leaf (5))))))) (.branch 51 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (4)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (6)) (.leaf (2))) (.branch 42 (.leaf (0)) (.leaf (3))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (7)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (5)) (.leaf (0))) (.branch 50 (.leaf (4)) (.leaf (0)))))) (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (2)) (.leaf (0))) (.branch 54 (.leaf (6)) (.leaf (1)))) (.branch 57 (.branch 56 (.leaf (0)) (.leaf (3))) (.branch 58 (.leaf (0)) (.leaf (5))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (2)) (.leaf (0))) (.branch 62 (.leaf (8)) (.leaf (0)))) (.branch 65 (.branch 64 (.leaf (4)) (.leaf (1))) (.branch 66 (.leaf (0)) (.leaf (6))))))))
  code := certificateP9_4907
  counts := ![(.branch 32 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 19 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 20 (.leaf (9)) (.leaf (10)))) (.branch 27 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.leaf (14)))))) (.branch 49 (.branch 39 (.branch 34 (.leaf (15)) (.branch 37 (.leaf (16)) (.leaf (17)))) (.branch 44 (.branch 42 (.leaf (18)) (.leaf (19))) (.branch 47 (.leaf (20)) (.leaf (21))))) (.branch 58 (.branch 53 (.branch 51 (.leaf (22)) (.leaf (23))) (.branch 56 (.leaf (24)) (.leaf (25)))) (.branch 63 (.branch 61 (.leaf (26)) (.leaf (27))) (.branch 66 (.leaf (28)) (.leaf (29))))))),
  (.branch 36 (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 55 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 65 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.leaf (7))))),
  (.branch 31 (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 40 (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 54 (.leaf (3)) (.branch 67 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 29 (.leaf (0)) (.branch 62 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))) (.branch 22 (.branch 20 (.leaf (-18)) (.leaf (-20))) (.branch 53 (.leaf (-22)) (.leaf (-23))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (-7))) (.branch 45 (.leaf (-13)) (.leaf (-15)))),
  (.branch 33 (.branch 4 (.leaf (0)) (.branch 23 (.leaf (-13)) (.leaf (-17)))) (.branch 41 (.leaf (-18)) (.branch 60 (.leaf (-23)) (.leaf (-27))))),
  (.branch 3 (.leaf (0)) (.branch 43 (.leaf (-21)) (.leaf (-22)))),
  (.branch 10 (.leaf (0)) (.branch 50 (.leaf (-7)) (.leaf (-8)))),
  (.branch 48 (.branch 7 (.leaf (0)) (.leaf (-7))) (.branch 59 (.leaf (-8)) (.leaf (-11)))),
  (.branch 13 (.leaf (0)) (.branch 40 (.leaf (-1)) (.leaf (-2)))),
  (.branch 12 (.leaf (0)) (.leaf (-43))),
  (.branch 29 (.leaf (0)) (.branch 62 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 59 (.branch 54 (.leaf (-23)) (.leaf (-22))) (.branch 64 (.leaf (-21)) (.leaf (-18)))),
  (.branch 56 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 66 (.leaf (-13)) (.leaf (-9)))),
  (.branch 63 (.branch 61 (.leaf (-27)) (.branch 62 (.leaf (-25)) (.leaf (-23)))) (.branch 65 (.branch 64 (.leaf (-21)) (.leaf (-19))) (.branch 66 (.leaf (-17)) (.leaf (-15))))),
  (.branch 61 (.branch 58 (.branch 44 (.leaf (-22)) (.leaf (-21))) (.branch 59 (.leaf (-19)) (.branch 60 (.leaf (-17)) (.leaf (-15))))) (.branch 64 (.branch 62 (.leaf (-13)) (.branch 63 (.leaf (-11)) (.leaf (-9)))) (.branch 65 (.leaf (-7)) (.branch 66 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 65 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 66 (.leaf (-5)) (.leaf (-3)))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-11)) (.leaf (-10))) (.branch 62 (.leaf (-9)) (.leaf (-8)))) (.branch 65 (.branch 64 (.leaf (-7)) (.leaf (-6))) (.branch 66 (.leaf (-5)) (.leaf (-4))))),
  (.branch 55 (.leaf (-2)) (.branch 56 (.leaf (-1)) (.leaf (0)))),
  (.branch 56 (.branch 50 (.branch 47 (.branch 13 (.leaf (-43)) (.leaf (-42))) (.branch 48 (.leaf (-40)) (.branch 49 (.leaf (-38)) (.leaf (-36))))) (.branch 53 (.branch 51 (.leaf (-34)) (.branch 52 (.leaf (-32)) (.leaf (-30)))) (.branch 54 (.leaf (-28)) (.branch 55 (.leaf (-26)) (.leaf (-24)))))) (.branch 61 (.branch 58 (.branch 57 (.leaf (-22)) (.leaf (-20))) (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-16)) (.leaf (-14))))) (.branch 64 (.branch 62 (.leaf (-12)) (.branch 63 (.leaf (-10)) (.leaf (-8)))) (.branch 65 (.leaf (-6)) (.branch 66 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 64 (.branch 63 (.leaf (-10)) (.leaf (-8))) (.branch 65 (.leaf (-6)) (.branch 66 (.leaf (-4)) (.leaf (-2)))))]
def witnessP9_289_4908 : CycleWitness 9 where
  length := 67
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (8))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (6))) (.branch 23 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (7)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (3)) (.leaf (2)))))))) (.branch 50 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (4))) (.branch 36 (.leaf (8)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (6)) (.leaf (0))) (.branch 40 (.leaf (5)) (.leaf (2))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (3)) (.leaf (1))) (.branch 44 (.leaf (0)) (.leaf (7)))) (.branch 47 (.branch 46 (.leaf (4)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 49 (.leaf (0)) (.leaf (3))))))) (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (5)) (.leaf (8))) (.branch 53 (.leaf (1)) (.leaf (0)))) (.branch 56 (.branch 55 (.leaf (6)) (.leaf (2))) (.branch 57 (.leaf (4)) (.leaf (0))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (1)) (.leaf (3))) (.branch 61 (.leaf (7)) (.leaf (5)))) (.branch 64 (.branch 63 (.leaf (0)) (.leaf (2))) (.branch 65 (.leaf (1)) (.branch 66 (.leaf (4)) (.leaf (8)))))))))
  code := certificateP9_4908
  counts := ![(.branch 29 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 39 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 41 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))) (.branch 57 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 66 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.branch 67 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-27))) (.branch 19 (.leaf (-31)) (.leaf (-37)))),
  (.branch 2 (.leaf (0)) (.branch 47 (.leaf (-15)) (.leaf (-19)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-11)) (.leaf (-18)))),
  (.branch 32 (.branch 3 (.leaf (0)) (.leaf (-27))) (.branch 50 (.leaf (-28)) (.leaf (-34)))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (-1))) (.branch 35 (.leaf (-3)) (.branch 66 (.leaf (-14)) (.leaf (-15))))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.branch 38 (.leaf (-47)) (.leaf (-49)))),
  (.branch 9 (.leaf (0)) (.branch 61 (.leaf (-17)) (.leaf (-18)))),
  (.branch 52 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 64 (.branch 20 (.leaf (-37)) (.branch 59 (.leaf (-36)) (.leaf (-35)))) (.branch 65 (.leaf (-28)) (.branch 66 (.leaf (-21)) (.leaf (-14))))),
  (.branch 54 (.branch 48 (.leaf (-19)) (.leaf (-18))) (.branch 60 (.leaf (-17)) (.branch 66 (.leaf (-16)) (.leaf (-12))))),
  (.branch 57 (.branch 18 (.leaf (-18)) (.branch 49 (.leaf (-17)) (.leaf (-16)))) (.branch 65 (.leaf (-15)) (.branch 66 (.leaf (-12)) (.leaf (-9))))),
  (.branch 63 (.branch 61 (.branch 51 (.leaf (-34)) (.leaf (-33))) (.branch 62 (.leaf (-29)) (.leaf (-25)))) (.branch 65 (.branch 64 (.leaf (-21)) (.leaf (-17))) (.branch 66 (.leaf (-13)) (.leaf (-9))))),
  (.leaf (-15)),
  (.branch 64 (.branch 63 (.leaf (-14)) (.leaf (-12))) (.branch 65 (.leaf (-10)) (.branch 66 (.leaf (-8)) (.leaf (-6))))),
  (.branch 60 (.branch 57 (.branch 39 (.leaf (-49)) (.branch 56 (.leaf (-48)) (.leaf (-44)))) (.branch 58 (.leaf (-40)) (.branch 59 (.leaf (-36)) (.leaf (-32))))) (.branch 63 (.branch 61 (.leaf (-28)) (.branch 62 (.leaf (-24)) (.leaf (-20)))) (.branch 65 (.branch 64 (.leaf (-16)) (.leaf (-12))) (.branch 66 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 64 (.branch 62 (.leaf (-18)) (.branch 63 (.leaf (-16)) (.leaf (-14)))) (.branch 65 (.leaf (-12)) (.branch 66 (.leaf (-10)) (.leaf (-8))))),
  (.branch 53 (.leaf (-1)) (.leaf (0)))]
def witnessP9_289_4909 : CycleWitness 9 where
  length := 67
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (5))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (0))) (.branch 11 (.leaf (7)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (8))) (.branch 15 (.leaf (2)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (3))) (.branch 19 (.leaf (5)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (6))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (7)) (.leaf (0))) (.branch 27 (.leaf (8)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (5)))))))) (.branch 50 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (2)) (.leaf (6))) (.branch 36 (.leaf (0)) (.leaf (3)))) (.branch 39 (.branch 38 (.leaf (7)) (.leaf (0))) (.branch 40 (.leaf (1)) (.leaf (8))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (4))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (5)) (.leaf (3))) (.branch 48 (.leaf (0)) (.branch 49 (.leaf (6)) (.leaf (1))))))) (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (7)) (.leaf (0))) (.branch 53 (.leaf (2)) (.leaf (8)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (3))) (.branch 57 (.leaf (4)) (.leaf (0))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (5)) (.leaf (1))) (.branch 61 (.leaf (0)) (.leaf (6)))) (.branch 64 (.branch 63 (.leaf (2)) (.leaf (0))) (.branch 65 (.leaf (7)) (.branch 66 (.leaf (3)) (.leaf (8)))))))))
  code := certificateP9_4909
  counts := ![(.branch 32 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 16 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))) (.branch 48 (.branch 39 (.branch 36 (.leaf (11)) (.leaf (12))) (.branch 42 (.leaf (13)) (.branch 45 (.leaf (14)) (.leaf (15))))) (.branch 58 (.branch 52 (.leaf (16)) (.branch 55 (.leaf (17)) (.leaf (18)))) (.branch 61 (.leaf (19)) (.branch 64 (.leaf (20)) (.leaf (21))))))),
  (.branch 31 (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.leaf (7))))),
  (.branch 34 (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.leaf (7))))),
  (.branch 37 (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 47 (.leaf (4)) (.leaf (5))) (.branch 66 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 62 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 65 (.leaf (4)) (.leaf (5))))),
  (.branch 41 (.branch 14 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 54 (.leaf (3)) (.branch 67 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-46)) (.leaf (-50)))) (.branch 13 (.branch 10 (.leaf (-54)) (.leaf (-58))) (.branch 16 (.leaf (-62)) (.leaf (-66))))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-53))) (.branch 40 (.leaf (-54)) (.leaf (-55)))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-32)) (.leaf (-33)))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 3 (.leaf (0)) (.branch 43 (.leaf (-52)) (.leaf (-53)))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (-37))) (.branch 59 (.leaf (-39)) (.leaf (-40)))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (-22))) (.branch 35 (.leaf (-24)) (.leaf (-26)))),
  (.branch 11 (.leaf (0)) (.branch 51 (.leaf (-12)) (.leaf (-13)))),
  (.leaf (0))]
  high := ![(.branch 49 (.branch 17 (.leaf (-66)) (.branch 33 (.leaf (-65)) (.leaf (-64)))) (.branch 65 (.leaf (-63)) (.branch 66 (.leaf (-42)) (.leaf (-21))))),
  (.branch 62 (.branch 51 (.branch 41 (.leaf (-55)) (.leaf (-52))) (.branch 61 (.leaf (-49)) (.leaf (-42)))) (.branch 64 (.branch 63 (.leaf (-35)) (.leaf (-28))) (.branch 65 (.leaf (-21)) (.branch 66 (.leaf (-14)) (.leaf (-7)))))),
  (.branch 64 (.branch 25 (.leaf (-33)) (.branch 54 (.leaf (-31)) (.leaf (-28)))) (.branch 65 (.leaf (-21)) (.branch 66 (.leaf (-14)) (.leaf (-7))))),
  (.branch 9 (.leaf (-11)) (.branch 57 (.leaf (-10)) (.leaf (-7)))),
  (.branch 61 (.branch 58 (.branch 44 (.leaf (-53)) (.leaf (-50))) (.branch 59 (.leaf (-45)) (.branch 60 (.leaf (-40)) (.leaf (-35))))) (.branch 64 (.branch 62 (.leaf (-30)) (.branch 63 (.leaf (-25)) (.leaf (-20)))) (.branch 65 (.leaf (-15)) (.branch 66 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 63 (.branch 61 (.branch 60 (.leaf (-40)) (.leaf (-35))) (.branch 62 (.leaf (-30)) (.leaf (-25)))) (.branch 65 (.branch 64 (.leaf (-20)) (.leaf (-15))) (.branch 66 (.leaf (-10)) (.leaf (-5))))),
  (.branch 64 (.branch 36 (.leaf (-26)) (.branch 63 (.leaf (-25)) (.leaf (-20)))) (.branch 65 (.leaf (-15)) (.branch 66 (.leaf (-10)) (.leaf (-5))))),
  (.branch 52 (.leaf (-13)) (.branch 66 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (0))]
def witnessP9_289_4910 : CycleWitness 9 where
  length := 67
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (7)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (8)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (4)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (7)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (5))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (4)) (.leaf (2)))))))) (.branch 50 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (5))) (.branch 36 (.leaf (3)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (6)) (.leaf (0))) (.branch 40 (.leaf (8)) (.leaf (2))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (4)) (.leaf (1))) (.branch 44 (.leaf (0)) (.leaf (3)))) (.branch 47 (.branch 46 (.leaf (5)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 49 (.leaf (0)) (.leaf (4))))))) (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (7)) (.leaf (3))) (.branch 53 (.leaf (1)) (.leaf (0)))) (.branch 56 (.branch 55 (.leaf (6)) (.leaf (2))) (.branch 57 (.leaf (5)) (.leaf (0))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (1)) (.leaf (4))) (.branch 61 (.leaf (3)) (.leaf (8)))) (.branch 64 (.branch 63 (.leaf (0)) (.leaf (2))) (.branch 65 (.leaf (1)) (.branch 66 (.leaf (5)) (.leaf (3)))))))))
  code := certificateP9_4910
  counts := ![(.branch 29 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 39 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 41 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.branch 67 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))) (.branch 57 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 66 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-27))) (.branch 19 (.leaf (-31)) (.leaf (-37)))),
  (.branch 2 (.leaf (0)) (.branch 47 (.leaf (-15)) (.leaf (-19)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-11)) (.leaf (-18)))),
  (.branch 52 (.leaf (0)) (.leaf (-4))),
  (.branch 32 (.branch 3 (.leaf (0)) (.leaf (-27))) (.branch 50 (.leaf (-28)) (.leaf (-34)))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (-1))) (.branch 35 (.leaf (-3)) (.branch 66 (.leaf (-14)) (.leaf (-15))))),
  (.branch 5 (.leaf (0)) (.branch 38 (.leaf (-47)) (.leaf (-49)))),
  (.branch 7 (.leaf (0)) (.branch 28 (.leaf (-31)) (.leaf (-34)))),
  (.branch 16 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 64 (.branch 20 (.leaf (-37)) (.branch 59 (.leaf (-36)) (.leaf (-35)))) (.branch 65 (.leaf (-28)) (.branch 66 (.leaf (-21)) (.leaf (-14))))),
  (.branch 54 (.branch 48 (.leaf (-19)) (.leaf (-18))) (.branch 60 (.leaf (-17)) (.branch 66 (.leaf (-16)) (.leaf (-12))))),
  (.branch 57 (.branch 18 (.leaf (-18)) (.branch 49 (.leaf (-17)) (.leaf (-16)))) (.branch 65 (.leaf (-15)) (.branch 66 (.leaf (-12)) (.leaf (-9))))),
  (.branch 53 (.leaf (-4)) (.branch 62 (.leaf (-3)) (.leaf (0)))),
  (.branch 63 (.branch 61 (.branch 51 (.leaf (-34)) (.leaf (-33))) (.branch 62 (.leaf (-29)) (.leaf (-25)))) (.branch 65 (.branch 64 (.leaf (-21)) (.leaf (-17))) (.branch 66 (.leaf (-13)) (.leaf (-9))))),
  (.leaf (-15)),
  (.branch 60 (.branch 57 (.branch 39 (.leaf (-49)) (.branch 56 (.leaf (-48)) (.leaf (-44)))) (.branch 58 (.leaf (-40)) (.branch 59 (.leaf (-36)) (.leaf (-32))))) (.branch 63 (.branch 61 (.leaf (-28)) (.branch 62 (.leaf (-24)) (.leaf (-20)))) (.branch 65 (.branch 64 (.leaf (-16)) (.leaf (-12))) (.branch 66 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 58 (.branch 54 (.branch 52 (.branch 29 (.leaf (-34)) (.leaf (-33))) (.branch 53 (.leaf (-31)) (.leaf (-29)))) (.branch 56 (.branch 55 (.leaf (-27)) (.leaf (-25))) (.branch 57 (.leaf (-23)) (.leaf (-21))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-19)) (.leaf (-17))) (.branch 61 (.leaf (-15)) (.leaf (-13)))) (.branch 64 (.branch 63 (.leaf (-11)) (.leaf (-9))) (.branch 65 (.leaf (-7)) (.branch 66 (.leaf (-5)) (.leaf (-3))))))),
  (.branch 64 (.branch 63 (.leaf (-7)) (.leaf (-6))) (.branch 65 (.leaf (-5)) (.branch 66 (.leaf (-4)) (.leaf (-3)))))]
def witnessP9_289_4911 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 13 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (0)))))) (.branch 25 (.branch 20 (.branch 18 (.leaf (4)) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (6))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (0)) (.leaf (2))))))) (.branch 50 (.branch 41 (.branch 37 (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (1)) (.leaf (0))) (.branch 40 (.leaf (3)) (.leaf (0))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (7)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (1)) (.leaf (0)))))) (.branch 58 (.branch 53 (.branch 51 (.leaf (4)) (.branch 52 (.leaf (0)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (2))) (.branch 57 (.leaf (0)) (.leaf (1))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (0)) (.leaf (5)))) (.branch 64 (.branch 63 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (0)) (.leaf (8))))))))
  code := certificateP9_4911
  counts := ![(.branch 32 (.branch 15 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.leaf (12)))) (.branch 26 (.branch 24 (.leaf (13)) (.leaf (14))) (.branch 28 (.leaf (15)) (.branch 30 (.leaf (16)) (.leaf (17))))))) (.branch 48 (.branch 39 (.branch 35 (.branch 34 (.leaf (18)) (.leaf (19))) (.branch 37 (.leaf (20)) (.leaf (21)))) (.branch 43 (.branch 41 (.leaf (22)) (.leaf (23))) (.branch 45 (.leaf (24)) (.branch 46 (.leaf (25)) (.leaf (26)))))) (.branch 57 (.branch 52 (.branch 50 (.leaf (27)) (.leaf (28))) (.branch 54 (.leaf (29)) (.branch 56 (.leaf (30)) (.leaf (31))))) (.branch 61 (.branch 59 (.leaf (32)) (.leaf (33))) (.branch 63 (.leaf (34)) (.branch 65 (.leaf (35)) (.leaf (36)))))))),
  (.branch 31 (.branch 14 (.branch 5 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 47 (.leaf (12)) (.leaf (13))))) (.branch 58 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2)))),
  (.branch 29 (.leaf (0)) (.branch 62 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1))),
  (.branch 66 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 27 (.branch 5 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 16 (.leaf (-3)) (.leaf (-4)))) (.branch 49 (.branch 38 (.leaf (-5)) (.leaf (-6))) (.branch 60 (.leaf (-7)) (.leaf (-8))))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.leaf (-26))),
  (.branch 18 (.leaf (0)) (.leaf (-15))),
  (.branch 29 (.leaf (0)) (.leaf (-4))),
  (.branch 22 (.leaf (0)) (.leaf (-44))),
  (.branch 44 (.leaf (0)) (.leaf (-22))),
  (.leaf (0))]
  high := ![(.branch 60 (.branch 58 (.leaf (-10)) (.leaf (-9))) (.branch 62 (.leaf (-8)) (.branch 64 (.leaf (-7)) (.leaf (-6))))),
  (.branch 65 (.leaf (-8)) (.leaf (-7))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.branch 46 (.branch 43 (.branch 41 (.leaf (-26)) (.branch 42 (.leaf (-25)) (.leaf (-24)))) (.branch 44 (.leaf (-23)) (.branch 45 (.leaf (-22)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18)))) (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))))) (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.branch 54 (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 44 (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (-44)) (.leaf (-43))) (.branch 25 (.leaf (-42)) (.branch 26 (.leaf (-41)) (.leaf (-40))))) (.branch 30 (.branch 28 (.leaf (-39)) (.branch 29 (.leaf (-38)) (.leaf (-37)))) (.branch 31 (.leaf (-36)) (.branch 32 (.leaf (-35)) (.leaf (-34)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (-33)) (.leaf (-32))) (.branch 36 (.leaf (-31)) (.branch 37 (.leaf (-30)) (.leaf (-29))))) (.branch 41 (.branch 39 (.leaf (-28)) (.branch 40 (.leaf (-27)) (.leaf (-26)))) (.branch 42 (.leaf (-25)) (.branch 43 (.leaf (-24)) (.leaf (-23))))))) (.branch 55 (.branch 49 (.branch 46 (.branch 45 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18))))) (.branch 52 (.branch 50 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 55 (.branch 49 (.branch 46 (.branch 45 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18))))) (.branch 52 (.branch 50 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_289_4912 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (2))) (.branch 16 (.leaf (0)) (.leaf (1)))))) (.branch 25 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (5)) (.leaf (1))))))) (.branch 50 (.branch 41 (.branch 37 (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (1))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (6))) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (2))) (.branch 49 (.leaf (0)) (.leaf (1)))))) (.branch 58 (.branch 53 (.branch 51 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (7)) (.leaf (1))) (.branch 57 (.leaf (0)) (.leaf (1))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (2)) (.leaf (0))) (.branch 61 (.leaf (1)) (.leaf (0)))) (.branch 64 (.branch 63 (.leaf (1)) (.leaf (0))) (.branch 65 (.leaf (8)) (.leaf (1))))))))
  code := certificateP9_4912
  counts := ![(.branch 31 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 18 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 20 (.leaf (9)) (.leaf (10)))) (.branch 27 (.branch 24 (.leaf (11)) (.leaf (12))) (.branch 29 (.leaf (13)) (.leaf (14)))))) (.branch 49 (.branch 40 (.branch 35 (.branch 34 (.leaf (15)) (.leaf (16))) (.branch 38 (.leaf (17)) (.leaf (18)))) (.branch 45 (.branch 42 (.leaf (19)) (.leaf (20))) (.branch 46 (.leaf (21)) (.leaf (22))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (23)) (.leaf (24))) (.branch 56 (.leaf (25)) (.leaf (26)))) (.branch 62 (.branch 60 (.leaf (27)) (.leaf (28))) (.branch 64 (.leaf (29)) (.leaf (30))))))),
  (.branch 33 (.branch 17 (.branch 8 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 28 (.leaf (9)) (.branch 30 (.leaf (10)) (.leaf (11)))))) (.branch 50 (.branch 41 (.branch 36 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14)))) (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17))))) (.branch 58 (.branch 52 (.leaf (18)) (.branch 55 (.leaf (19)) (.leaf (20)))) (.branch 63 (.branch 61 (.leaf (21)) (.leaf (22))) (.branch 66 (.leaf (23)) (.leaf (24))))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1))),
  (.branch 65 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 24 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 13 (.leaf (-10)) (.leaf (-11)))) (.branch 46 (.branch 35 (.leaf (-12)) (.leaf (-13))) (.branch 57 (.leaf (-14)) (.leaf (-15))))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-56))),
  (.branch 21 (.leaf (0)) (.leaf (-45))),
  (.branch 32 (.leaf (0)) (.leaf (-34))),
  (.branch 43 (.leaf (0)) (.leaf (-23))),
  (.branch 54 (.leaf (0)) (.leaf (-12))),
  (.branch 65 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 58 (.leaf (-15)) (.branch 65 (.leaf (-14)) (.leaf (-10)))),
  (.branch 64 (.leaf (-1)) (.leaf (0))),
  (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.branch 24 (.branch 17 (.branch 13 (.branch 11 (.leaf (-56)) (.branch 12 (.leaf (-55)) (.leaf (-54)))) (.branch 15 (.branch 14 (.leaf (-53)) (.leaf (-52))) (.branch 16 (.leaf (-51)) (.leaf (-50))))) (.branch 20 (.branch 18 (.leaf (-49)) (.branch 19 (.leaf (-48)) (.leaf (-47)))) (.branch 22 (.branch 21 (.leaf (-46)) (.leaf (-45))) (.branch 23 (.leaf (-44)) (.leaf (-43)))))) (.branch 31 (.branch 27 (.branch 25 (.leaf (-42)) (.branch 26 (.leaf (-41)) (.leaf (-40)))) (.branch 29 (.branch 28 (.leaf (-39)) (.leaf (-38))) (.branch 30 (.leaf (-37)) (.leaf (-36))))) (.branch 34 (.branch 32 (.leaf (-35)) (.branch 33 (.leaf (-34)) (.leaf (-33)))) (.branch 36 (.branch 35 (.leaf (-32)) (.leaf (-31))) (.branch 37 (.leaf (-30)) (.leaf (-29))))))) (.branch 52 (.branch 45 (.branch 41 (.branch 39 (.leaf (-28)) (.branch 40 (.leaf (-27)) (.leaf (-26)))) (.branch 43 (.branch 42 (.leaf (-25)) (.leaf (-24))) (.branch 44 (.leaf (-23)) (.leaf (-22))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19)))) (.branch 50 (.branch 49 (.leaf (-18)) (.leaf (-17))) (.branch 51 (.leaf (-16)) (.leaf (-15)))))) (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (-45)) (.leaf (-44))) (.branch 24 (.leaf (-43)) (.branch 25 (.leaf (-42)) (.leaf (-41))))) (.branch 29 (.branch 27 (.leaf (-40)) (.branch 28 (.leaf (-39)) (.leaf (-38)))) (.branch 30 (.leaf (-37)) (.branch 31 (.leaf (-36)) (.leaf (-35)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (-34)) (.leaf (-33))) (.branch 35 (.leaf (-32)) (.branch 36 (.leaf (-31)) (.leaf (-30))))) (.branch 40 (.branch 38 (.leaf (-29)) (.branch 39 (.leaf (-28)) (.leaf (-27)))) (.branch 41 (.leaf (-26)) (.branch 42 (.leaf (-25)) (.leaf (-24))))))) (.branch 54 (.branch 48 (.branch 45 (.branch 44 (.leaf (-23)) (.leaf (-22))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19))))) (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-34)) (.leaf (-33))) (.branch 35 (.leaf (-32)) (.leaf (-31)))) (.branch 38 (.branch 37 (.leaf (-30)) (.leaf (-29))) (.branch 39 (.leaf (-28)) (.leaf (-27))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-26)) (.leaf (-25))) (.branch 43 (.leaf (-24)) (.leaf (-23)))) (.branch 46 (.branch 45 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18))))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))) (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.leaf (-10))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 54 (.branch 48 (.branch 45 (.branch 44 (.leaf (-23)) (.leaf (-22))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19))))) (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_289_4913 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (4))) (.branch 16 (.leaf (0)) (.leaf (2)))))) (.branch 25 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (5)) (.leaf (2))))))) (.branch 50 (.branch 41 (.branch 37 (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (4)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 40 (.leaf (0)) (.leaf (1))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (7))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (3))) (.branch 49 (.leaf (0)) (.leaf (2)))))) (.branch 58 (.branch 53 (.branch 51 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (5)) (.leaf (2))) (.branch 57 (.leaf (0)) (.leaf (1))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (4)) (.leaf (0))) (.branch 61 (.leaf (2)) (.leaf (0)))) (.branch 64 (.branch 63 (.leaf (1)) (.leaf (0))) (.branch 65 (.leaf (8)) (.leaf (2))))))))
  code := certificateP9_4913
  counts := ![(.branch 31 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 18 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 20 (.leaf (9)) (.leaf (10)))) (.branch 27 (.branch 24 (.leaf (11)) (.leaf (12))) (.branch 29 (.leaf (13)) (.leaf (14)))))) (.branch 49 (.branch 40 (.branch 35 (.branch 34 (.leaf (15)) (.leaf (16))) (.branch 38 (.leaf (17)) (.leaf (18)))) (.branch 45 (.branch 42 (.leaf (19)) (.leaf (20))) (.branch 46 (.leaf (21)) (.leaf (22))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (23)) (.leaf (24))) (.branch 56 (.leaf (25)) (.leaf (26)))) (.branch 62 (.branch 60 (.leaf (27)) (.leaf (28))) (.branch 64 (.leaf (29)) (.leaf (30))))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 39 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 61 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1))),
  (.branch 65 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 24 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 13 (.leaf (-10)) (.leaf (-11)))) (.branch 46 (.branch 35 (.leaf (-12)) (.leaf (-13))) (.branch 57 (.leaf (-14)) (.leaf (-15))))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-18))),
  (.branch 15 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-12))),
  (.branch 21 (.leaf (0)) (.leaf (-45))),
  (.branch 43 (.leaf (0)) (.leaf (-23))),
  (.branch 65 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 58 (.leaf (-15)) (.branch 65 (.leaf (-14)) (.leaf (-10)))),
  (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 57 (.branch 52 (.branch 50 (.branch 49 (.leaf (-18)) (.leaf (-17))) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 54 (.branch 53 (.leaf (-14)) (.leaf (-13))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 43 (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (-45)) (.leaf (-44))) (.branch 24 (.leaf (-43)) (.branch 25 (.leaf (-42)) (.leaf (-41))))) (.branch 29 (.branch 27 (.leaf (-40)) (.branch 28 (.leaf (-39)) (.leaf (-38)))) (.branch 30 (.leaf (-37)) (.branch 31 (.leaf (-36)) (.leaf (-35)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (-34)) (.leaf (-33))) (.branch 35 (.leaf (-32)) (.branch 36 (.leaf (-31)) (.leaf (-30))))) (.branch 40 (.branch 38 (.leaf (-29)) (.branch 39 (.leaf (-28)) (.leaf (-27)))) (.branch 41 (.leaf (-26)) (.branch 42 (.leaf (-25)) (.leaf (-24))))))) (.branch 54 (.branch 48 (.branch 45 (.branch 44 (.leaf (-23)) (.leaf (-22))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19))))) (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 54 (.branch 48 (.branch 45 (.branch 44 (.leaf (-23)) (.leaf (-22))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19))))) (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_289_4914 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (5)))))) (.branch 25 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (7)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (3))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (1)) (.leaf (4))) (.branch 28 (.leaf (0)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (8))) (.branch 32 (.leaf (0)) (.leaf (3))))))) (.branch 50 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (5)) (.leaf (1))) (.branch 40 (.leaf (3)) (.leaf (0))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (6)) (.leaf (2))) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (3)) (.leaf (1))) (.branch 49 (.leaf (4)) (.leaf (0)))))) (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (2)) (.leaf (1))) (.branch 53 (.leaf (7)) (.leaf (0)))) (.branch 56 (.branch 55 (.leaf (3)) (.leaf (0))) (.branch 57 (.leaf (1)) (.leaf (2))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (0)) (.leaf (5))) (.branch 61 (.leaf (1)) (.leaf (3)))) (.branch 64 (.branch 63 (.leaf (0)) (.leaf (8))) (.branch 65 (.leaf (2)) (.leaf (1))))))))
  code := certificateP9_4914
  counts := ![(.branch 32 (.branch 12 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 15 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 28 (.leaf (9)) (.leaf (10)))))) (.branch 46 (.branch 37 (.branch 34 (.leaf (11)) (.leaf (12))) (.branch 41 (.leaf (13)) (.branch 45 (.leaf (14)) (.leaf (15))))) (.branch 56 (.branch 50 (.leaf (16)) (.branch 54 (.leaf (17)) (.leaf (18)))) (.branch 59 (.leaf (19)) (.branch 63 (.leaf (20)) (.leaf (21))))))),
  (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))) (.branch 52 (.branch 44 (.branch 39 (.leaf (8)) (.leaf (9))) (.branch 48 (.leaf (10)) (.leaf (11)))) (.branch 61 (.branch 57 (.leaf (12)) (.leaf (13))) (.branch 66 (.leaf (14)) (.leaf (15)))))),
  (.branch 36 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 33 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 53 (.leaf (1)) (.leaf (2)))),
  (.branch 31 (.leaf (0)) (.branch 64 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 24 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 12 (.leaf (-10)) (.branch 15 (.leaf (-11)) (.leaf (-12))))) (.branch 46 (.branch 34 (.leaf (-15)) (.branch 37 (.leaf (-16)) (.leaf (-17)))) (.branch 56 (.leaf (-20)) (.branch 59 (.leaf (-21)) (.leaf (-22)))))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-2)) (.leaf (-4)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 16 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-24))),
  (.branch 20 (.leaf (0)) (.leaf (-13))),
  (.branch 31 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 64 (.branch 60 (.leaf (-22)) (.leaf (-21))) (.branch 65 (.leaf (-19)) (.leaf (-17)))),
  (.branch 53 (.leaf (-4)) (.branch 62 (.leaf (-3)) (.leaf (0)))),
  (.leaf (-3)),
  (.branch 63 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))) (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.leaf (-10))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 48 (.branch 45 (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22)))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19))))) (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 65 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_289_4915 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (6)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (3))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (5)) (.leaf (0))) (.branch 40 (.leaf (1)) (.leaf (7))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (1)) (.leaf (4)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (3)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (2))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (5)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (8))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (1)) (.leaf (2)))))))))
  code := certificateP9_4915
  counts := ![(.branch 31 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))) (.branch 47 (.branch 39 (.branch 34 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14)))) (.branch 42 (.leaf (15)) (.branch 45 (.leaf (16)) (.leaf (17))))) (.branch 56 (.branch 50 (.leaf (18)) (.branch 53 (.leaf (19)) (.leaf (20)))) (.branch 61 (.branch 58 (.leaf (21)) (.leaf (22))) (.branch 64 (.leaf (23)) (.leaf (24))))))),
  (.branch 32 (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 26 (.leaf (9)) (.branch 29 (.leaf (10)) (.leaf (11)))))) (.branch 48 (.branch 40 (.branch 35 (.leaf (12)) (.branch 37 (.leaf (13)) (.leaf (14)))) (.branch 43 (.leaf (15)) (.branch 46 (.leaf (16)) (.leaf (17))))) (.branch 57 (.branch 51 (.leaf (18)) (.branch 54 (.leaf (19)) (.leaf (20)))) (.branch 62 (.branch 59 (.leaf (21)) (.leaf (22))) (.branch 65 (.leaf (23)) (.leaf (24))))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1))),
  (.branch 63 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 16 (.leaf (0)) (.leaf (-6))),
  (.branch 19 (.leaf (0)) (.leaf (-47))),
  (.branch 41 (.leaf (0)) (.leaf (-25))),
  (.branch 63 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 62 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.branch 60 (.leaf (-6)) (.branch 63 (.leaf (-5)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))) (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.leaf (-10))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 30 (.branch 24 (.branch 21 (.branch 20 (.leaf (-47)) (.leaf (-46))) (.branch 22 (.leaf (-45)) (.branch 23 (.leaf (-44)) (.leaf (-43))))) (.branch 27 (.branch 25 (.leaf (-42)) (.branch 26 (.leaf (-41)) (.leaf (-40)))) (.branch 28 (.leaf (-39)) (.branch 29 (.leaf (-38)) (.leaf (-37)))))) (.branch 36 (.branch 33 (.branch 31 (.leaf (-36)) (.branch 32 (.leaf (-35)) (.leaf (-34)))) (.branch 34 (.leaf (-33)) (.branch 35 (.leaf (-32)) (.leaf (-31))))) (.branch 39 (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-29)) (.leaf (-28)))) (.branch 40 (.leaf (-27)) (.branch 41 (.leaf (-26)) (.leaf (-25))))))) (.branch 54 (.branch 48 (.branch 45 (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22)))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19))))) (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 53 (.branch 47 (.branch 44 (.branch 42 (.leaf (-25)) (.branch 43 (.leaf (-24)) (.leaf (-23)))) (.branch 45 (.leaf (-22)) (.branch 46 (.leaf (-21)) (.leaf (-20))))) (.branch 50 (.branch 48 (.leaf (-19)) (.branch 49 (.leaf (-18)) (.leaf (-17)))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-15)) (.leaf (-14)))))) (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_289_4916 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (6)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (7))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (0))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (8)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (3)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (5)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (6)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (2)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (1)) (.leaf (4))) (.branch 52 (.leaf (0)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (7))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (3))) (.branch 60 (.leaf (0)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (5)) (.leaf (0))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (0)) (.leaf (8)))))))))
  code := certificateP9_4916
  counts := ![(.branch 32 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 19 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 21 (.leaf (9)) (.leaf (10)))) (.branch 27 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.leaf (14)))))) (.branch 49 (.branch 41 (.branch 36 (.branch 34 (.leaf (15)) (.leaf (16))) (.branch 38 (.leaf (17)) (.leaf (18)))) (.branch 45 (.branch 43 (.leaf (19)) (.leaf (20))) (.branch 47 (.leaf (21)) (.leaf (22))))) (.branch 58 (.branch 54 (.branch 52 (.leaf (23)) (.leaf (24))) (.branch 56 (.leaf (25)) (.leaf (26)))) (.branch 63 (.branch 60 (.leaf (27)) (.leaf (28))) (.branch 65 (.leaf (29)) (.leaf (30))))))),
  (.branch 31 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 50 (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 61 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2)))),
  (.branch 33 (.leaf (0)) (.branch 66 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-18))),
  (.branch 15 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 18 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-22))),
  (.branch 22 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 61 (.leaf (-8)) (.leaf (-5))),
  (.branch 65 (.leaf (-6)) (.leaf (-3))),
  (.branch 57 (.branch 52 (.branch 50 (.branch 49 (.leaf (-18)) (.leaf (-17))) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 54 (.branch 53 (.leaf (-14)) (.leaf (-13))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 54 (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.branch 49 (.branch 46 (.branch 45 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18))))) (.branch 52 (.branch 50 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_289_4917 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (6))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (3)) (.leaf (0))) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (7)) (.leaf (5))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (8)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (6))) (.branch 44 (.leaf (5)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (2)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (3)) (.leaf (0))) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (7)) (.leaf (4))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (2))) (.branch 60 (.leaf (0)) (.leaf (3)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (8)) (.leaf (5)))))))))
  code := certificateP9_4917
  counts := ![(.branch 31 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 18 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 20 (.leaf (9)) (.leaf (10)))) (.branch 27 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 29 (.leaf (13)) (.leaf (14)))))) (.branch 49 (.branch 40 (.branch 36 (.branch 34 (.leaf (15)) (.leaf (16))) (.branch 38 (.leaf (17)) (.leaf (18)))) (.branch 45 (.branch 42 (.leaf (19)) (.leaf (20))) (.branch 47 (.leaf (21)) (.leaf (22))))) (.branch 58 (.branch 53 (.branch 51 (.leaf (23)) (.leaf (24))) (.branch 56 (.leaf (25)) (.leaf (26)))) (.branch 62 (.branch 60 (.leaf (27)) (.leaf (28))) (.branch 64 (.leaf (29)) (.leaf (30))))))),
  (.branch 30 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2)))),
  (.branch 32 (.leaf (0)) (.branch 65 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-6)) (.leaf (-7)))) (.branch 7 (.leaf (-8)) (.branch 9 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-23))),
  (.branch 21 (.leaf (0)) (.leaf (-12))),
  (.branch 32 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 65 (.leaf (-10)) (.leaf (-5))),
  (.branch 64 (.branch 58 (.leaf (-7)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 54 (.branch 48 (.branch 45 (.branch 44 (.leaf (-23)) (.leaf (-22))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19))))) (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_289_4918 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (7))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (8)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (7)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (8))) (.branch 40 (.leaf (1)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (6)) (.leaf (0))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (4)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (7)) (.leaf (1))) (.branch 52 (.leaf (0)) (.leaf (5)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (2))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (3))) (.branch 60 (.leaf (0)) (.leaf (8)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (0))) (.branch 64 (.leaf (6)) (.branch 65 (.leaf (0)) (.leaf (4)))))))))
  code := certificateP9_4918
  counts := ![(.branch 32 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 19 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 21 (.leaf (9)) (.leaf (10)))) (.branch 27 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.leaf (14)))))) (.branch 49 (.branch 41 (.branch 36 (.branch 34 (.leaf (15)) (.leaf (16))) (.branch 38 (.leaf (17)) (.leaf (18)))) (.branch 45 (.branch 43 (.leaf (19)) (.leaf (20))) (.branch 47 (.leaf (21)) (.leaf (22))))) (.branch 58 (.branch 54 (.branch 52 (.leaf (23)) (.leaf (24))) (.branch 56 (.leaf (25)) (.leaf (26)))) (.branch 63 (.branch 60 (.leaf (27)) (.leaf (28))) (.branch 65 (.leaf (29)) (.leaf (30))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.branch 37 (.leaf (-13)) (.leaf (-14)))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (-6))) (.branch 59 (.leaf (-8)) (.leaf (-9)))),
  (.branch 15 (.leaf (0)) (.branch 48 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 20 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 61 (.leaf (-8)) (.leaf (-5))),
  (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 60 (.branch 57 (.branch 38 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 58 (.leaf (-11)) (.branch 59 (.leaf (-10)) (.leaf (-9))))) (.branch 63 (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6)))) (.branch 64 (.leaf (-5)) (.branch 65 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 62 (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7)))) (.branch 64 (.branch 63 (.leaf (-6)) (.leaf (-5))) (.branch 65 (.leaf (-4)) (.leaf (-3))))),
  (.branch 50 (.branch 49 (.leaf (-3)) (.leaf (-2))) (.branch 51 (.leaf (-1)) (.leaf (0)))),
  (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 65 (.leaf (-2)) (.leaf (-1))),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_289_4919 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (7)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (8))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (5)) (.leaf (0))) (.branch 40 (.leaf (1)) (.leaf (6))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (2))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (2)) (.leaf (4)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (7)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (3))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (2))) (.branch 60 (.leaf (5)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (8))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (2)) (.leaf (3)))))))))
  code := certificateP9_4919
  counts := ![(.branch 31 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))) (.branch 47 (.branch 39 (.branch 34 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14)))) (.branch 42 (.leaf (15)) (.branch 45 (.leaf (16)) (.leaf (17))))) (.branch 56 (.branch 50 (.leaf (18)) (.branch 53 (.leaf (19)) (.leaf (20)))) (.branch 61 (.branch 58 (.leaf (21)) (.leaf (22))) (.branch 64 (.leaf (23)) (.leaf (24))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.branch 63 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 16 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-25))),
  (.branch 19 (.leaf (0)) (.leaf (-14))),
  (.branch 30 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 62 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 60 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))) (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.leaf (-10))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 47 (.branch 44 (.branch 42 (.leaf (-25)) (.branch 43 (.leaf (-24)) (.leaf (-23)))) (.branch 45 (.leaf (-22)) (.branch 46 (.leaf (-21)) (.leaf (-20))))) (.branch 50 (.branch 48 (.leaf (-19)) (.branch 49 (.leaf (-18)) (.leaf (-17)))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-15)) (.leaf (-14)))))) (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_289_4920 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (6))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (0))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (4)) (.leaf (0))) (.branch 40 (.leaf (7)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (2)) (.leaf (4)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (5))) (.branch 52 (.leaf (0)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (3))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (2))) (.branch 60 (.leaf (4)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (8)) (.leaf (0))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (0)) (.leaf (3)))))))))
  code := certificateP9_4920
  counts := ![(.branch 32 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 21 (.leaf (9)) (.leaf (10)))) (.branch 28 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.leaf (14)))))) (.branch 50 (.branch 41 (.branch 36 (.branch 34 (.leaf (15)) (.leaf (16))) (.branch 39 (.leaf (17)) (.leaf (18)))) (.branch 45 (.branch 43 (.leaf (19)) (.leaf (20))) (.branch 47 (.leaf (21)) (.leaf (22))))) (.branch 58 (.branch 54 (.branch 52 (.leaf (23)) (.leaf (24))) (.branch 56 (.leaf (25)) (.leaf (26)))) (.branch 63 (.branch 61 (.leaf (27)) (.leaf (28))) (.branch 65 (.leaf (29)) (.leaf (30))))))),
  (.branch 31 (.branch 13 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 62 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-6)) (.leaf (-7)))),
  (.branch 24 (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))) (.branch 46 (.branch 35 (.leaf (-6)) (.leaf (-7))) (.branch 57 (.leaf (-8)) (.leaf (-9))))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 18 (.leaf (0)) (.leaf (-48))),
  (.branch 40 (.leaf (0)) (.leaf (-26))),
  (.branch 62 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 59 (.leaf (-7)) (.leaf (-5))),
  (.branch 58 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7)))),
  (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 54 (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 30 (.branch 24 (.branch 21 (.branch 19 (.leaf (-48)) (.branch 20 (.leaf (-47)) (.leaf (-46)))) (.branch 22 (.leaf (-45)) (.branch 23 (.leaf (-44)) (.leaf (-43))))) (.branch 27 (.branch 25 (.leaf (-42)) (.branch 26 (.leaf (-41)) (.leaf (-40)))) (.branch 28 (.leaf (-39)) (.branch 29 (.leaf (-38)) (.leaf (-37)))))) (.branch 36 (.branch 33 (.branch 31 (.leaf (-36)) (.branch 32 (.leaf (-35)) (.leaf (-34)))) (.branch 34 (.leaf (-33)) (.branch 35 (.leaf (-32)) (.leaf (-31))))) (.branch 39 (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-29)) (.leaf (-28)))) (.branch 40 (.leaf (-27)) (.branch 41 (.leaf (-26)) (.leaf (-25))))))) (.branch 54 (.branch 48 (.branch 45 (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22)))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19))))) (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 53 (.branch 46 (.branch 43 (.branch 41 (.leaf (-26)) (.branch 42 (.leaf (-25)) (.leaf (-24)))) (.branch 44 (.leaf (-23)) (.branch 45 (.leaf (-22)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18)))) (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))))) (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_289_4921 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (7)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (2))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (1)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (0)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (5)) (.leaf (0))) (.branch 40 (.leaf (2)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (4))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (2)) (.leaf (8)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (1))) (.branch 56 (.leaf (0)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (5)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (4)) (.leaf (2)))))))))
  code := certificateP9_4921
  counts := ![(.branch 31 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))) (.branch 47 (.branch 39 (.branch 34 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14)))) (.branch 42 (.leaf (15)) (.branch 45 (.leaf (16)) (.leaf (17))))) (.branch 56 (.branch 50 (.leaf (18)) (.branch 53 (.leaf (19)) (.leaf (20)))) (.branch 61 (.branch 58 (.leaf (21)) (.leaf (22))) (.branch 64 (.leaf (23)) (.leaf (24))))))),
  (.branch 33 (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 51 (.branch 41 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 59 (.branch 55 (.leaf (12)) (.leaf (13))) (.branch 63 (.leaf (14)) (.leaf (15)))))),
  (.branch 35 (.branch 18 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))) (.branch 52 (.branch 44 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 48 (.leaf (10)) (.leaf (11)))) (.branch 62 (.branch 57 (.leaf (12)) (.leaf (13))) (.branch 66 (.leaf (14)) (.leaf (15)))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 43 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))) (.branch 41 (.leaf (-7)) (.branch 63 (.leaf (-8)) (.leaf (-9))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 30 (.leaf (-2)) (.branch 52 (.leaf (-3)) (.leaf (-4))))),
  (.branch 10 (.leaf (0)) (.leaf (-12))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 16 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-61))),
  (.branch 27 (.leaf (0)) (.leaf (-39))),
  (.branch 49 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 62 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-7)) (.leaf (-5)))),
  (.branch 58 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (0)))),
  (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 20 (.branch 12 (.branch 8 (.branch 6 (.leaf (-61)) (.branch 7 (.leaf (-60)) (.leaf (-59)))) (.branch 10 (.branch 9 (.leaf (-58)) (.leaf (-57))) (.branch 11 (.leaf (-56)) (.leaf (-55))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-54)) (.leaf (-53))) (.branch 15 (.leaf (-52)) (.leaf (-51)))) (.branch 18 (.branch 17 (.leaf (-50)) (.leaf (-49))) (.branch 19 (.leaf (-48)) (.leaf (-47)))))) (.branch 27 (.branch 23 (.branch 21 (.leaf (-46)) (.branch 22 (.leaf (-45)) (.leaf (-44)))) (.branch 25 (.branch 24 (.leaf (-43)) (.leaf (-42))) (.branch 26 (.leaf (-41)) (.leaf (-40))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-39)) (.leaf (-38))) (.branch 30 (.leaf (-37)) (.leaf (-36)))) (.branch 33 (.branch 32 (.leaf (-35)) (.leaf (-34))) (.branch 34 (.leaf (-33)) (.leaf (-32))))))) (.branch 50 (.branch 42 (.branch 38 (.branch 36 (.leaf (-31)) (.branch 37 (.leaf (-30)) (.leaf (-29)))) (.branch 40 (.branch 39 (.leaf (-28)) (.leaf (-27))) (.branch 41 (.leaf (-26)) (.leaf (-25))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-24)) (.leaf (-23))) (.branch 45 (.leaf (-22)) (.leaf (-21)))) (.branch 48 (.branch 47 (.leaf (-20)) (.leaf (-19))) (.branch 49 (.leaf (-18)) (.leaf (-17)))))) (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 46 (.branch 36 (.branch 31 (.branch 29 (.branch 28 (.leaf (-39)) (.leaf (-38))) (.branch 30 (.leaf (-37)) (.leaf (-36)))) (.branch 33 (.branch 32 (.leaf (-35)) (.leaf (-34))) (.branch 34 (.leaf (-33)) (.branch 35 (.leaf (-32)) (.leaf (-31)))))) (.branch 41 (.branch 38 (.branch 37 (.leaf (-30)) (.leaf (-29))) (.branch 39 (.leaf (-28)) (.branch 40 (.leaf (-27)) (.leaf (-26))))) (.branch 43 (.branch 42 (.leaf (-25)) (.leaf (-24))) (.branch 44 (.leaf (-23)) (.branch 45 (.leaf (-22)) (.leaf (-21))))))) (.branch 56 (.branch 51 (.branch 48 (.branch 47 (.leaf (-20)) (.leaf (-19))) (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16))))) (.branch 53 (.branch 52 (.leaf (-15)) (.leaf (-14))) (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))))) (.branch 61 (.branch 58 (.branch 57 (.leaf (-10)) (.leaf (-9))) (.branch 59 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6))))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))) (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.leaf (-10))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_289_4922 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (3)) (.leaf (8)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (6)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (7)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (5))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (8)) (.leaf (0))) (.branch 40 (.leaf (3)) (.leaf (6))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (0))) (.branch 48 (.leaf (3)) (.leaf (7)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (5)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (4))) (.branch 56 (.leaf (0)) (.leaf (3))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (8)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (6))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (3)) (.leaf (4)))))))))
  code := certificateP9_4922
  counts := ![(.branch 31 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))) (.branch 47 (.branch 39 (.branch 34 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14)))) (.branch 42 (.leaf (15)) (.branch 45 (.leaf (16)) (.leaf (17))))) (.branch 56 (.branch 50 (.leaf (18)) (.branch 53 (.leaf (19)) (.leaf (20)))) (.branch 61 (.branch 58 (.leaf (21)) (.leaf (22))) (.branch 64 (.leaf (23)) (.leaf (24))))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 65 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-25))) (.branch 18 (.leaf (-26)) (.branch 26 (.leaf (-27)) (.leaf (-28))))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 19 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 16 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 62 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.branch 62 (.branch 60 (.leaf (-28)) (.branch 61 (.leaf (-24)) (.leaf (-20)))) (.branch 64 (.branch 63 (.leaf (-16)) (.leaf (-12))) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 63 (.branch 38 (.leaf (-17)) (.leaf (-16))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 49 (.leaf (-6)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))) (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.leaf (-10))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_289_4923 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (6)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (3))) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (7))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (3))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (8)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (0)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (5)) (.leaf (0))) (.branch 40 (.leaf (3)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (2))) (.branch 44 (.leaf (6)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (4)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (2))) (.branch 52 (.leaf (3)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (7))) (.branch 56 (.leaf (0)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (5)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (3)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (2)) (.leaf (8)))))))))
  code := certificateP9_4923
  counts := ![(.branch 31 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))) (.branch 47 (.branch 39 (.branch 34 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14)))) (.branch 42 (.leaf (15)) (.branch 45 (.leaf (16)) (.leaf (17))))) (.branch 56 (.branch 50 (.leaf (18)) (.branch 53 (.leaf (19)) (.leaf (20)))) (.branch 61 (.branch 58 (.leaf (21)) (.leaf (22))) (.branch 64 (.leaf (23)) (.leaf (24))))))),
  (.branch 32 (.branch 15 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 49 (.branch 41 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 59 (.branch 54 (.leaf (12)) (.leaf (13))) (.branch 63 (.leaf (14)) (.leaf (15)))))),
  (.branch 35 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2)))),
  (.branch 33 (.leaf (0)) (.branch 66 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 27 (.leaf (-8)) (.branch 49 (.leaf (-9)) (.leaf (-10))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 35 (.leaf (-4)) (.branch 57 (.leaf (-5)) (.leaf (-6))))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-18))),
  (.branch 16 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.leaf (-22))),
  (.branch 22 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 62 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.branch 64 (.branch 50 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-7)) (.leaf (-5)))),
  (.branch 58 (.leaf (-6)) (.leaf (-5))),
  (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 52 (.branch 50 (.branch 49 (.leaf (-18)) (.leaf (-17))) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 54 (.branch 53 (.leaf (-14)) (.leaf (-13))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 49 (.branch 46 (.branch 45 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18))))) (.branch 52 (.branch 50 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_289_4924 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (4))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (3)) (.leaf (0))) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (7))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (1)) (.leaf (3))) (.branch 40 (.leaf (0)) (.leaf (6))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (5))) (.branch 48 (.leaf (1)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (3)) (.leaf (0))) (.branch 52 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (8))) (.branch 56 (.leaf (1)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (4)) (.leaf (0))) (.branch 60 (.leaf (1)) (.leaf (3)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (2))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (0)) (.leaf (5)))))))))
  code := certificateP9_4924
  counts := ![(.branch 32 (.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 26 (.leaf (9)) (.branch 29 (.leaf (10)) (.leaf (11)))))) (.branch 49 (.branch 40 (.branch 34 (.leaf (12)) (.branch 37 (.leaf (13)) (.leaf (14)))) (.branch 43 (.leaf (15)) (.branch 46 (.leaf (16)) (.leaf (17))))) (.branch 57 (.branch 51 (.leaf (18)) (.branch 54 (.leaf (19)) (.leaf (20)))) (.branch 62 (.branch 59 (.leaf (21)) (.leaf (22))) (.branch 65 (.leaf (23)) (.leaf (24))))))),
  (.branch 31 (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 38 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 44 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 30 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 47 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 55 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 26 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 34 (.leaf (-10)) (.branch 59 (.leaf (-12)) (.leaf (-13))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 11 (.leaf (-16)) (.branch 44 (.leaf (-26)) (.leaf (-35))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 36 (.leaf (-7)) (.branch 53 (.leaf (-9)) (.leaf (-10))))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 14 (.leaf (0)) (.branch 33 (.leaf (-10)) (.leaf (-15)))),
  (.branch 47 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-25))),
  (.branch 22 (.leaf (0)) (.leaf (-44))),
  (.branch 55 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 60 (.leaf (-13)) (.branch 63 (.leaf (-12)) (.leaf (-11)))),
  (.branch 53 (.branch 45 (.leaf (-35)) (.branch 49 (.leaf (-34)) (.leaf (-33)))) (.branch 61 (.branch 57 (.leaf (-32)) (.leaf (-31))) (.branch 65 (.leaf (-30)) (.leaf (-24))))),
  (.branch 64 (.branch 54 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-7)))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 61 (.branch 59 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 60 (.leaf (-13)) (.leaf (-12)))) (.branch 63 (.branch 62 (.leaf (-11)) (.leaf (-10))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7)))))),
  (.branch 48 (.leaf (-1)) (.leaf (0))),
  (.branch 53 (.branch 47 (.branch 44 (.branch 42 (.leaf (-25)) (.branch 43 (.leaf (-24)) (.leaf (-23)))) (.branch 45 (.leaf (-22)) (.branch 46 (.leaf (-21)) (.leaf (-20))))) (.branch 50 (.branch 48 (.leaf (-19)) (.branch 49 (.leaf (-18)) (.leaf (-17)))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-15)) (.leaf (-14)))))) (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (-44)) (.leaf (-43))) (.branch 25 (.leaf (-42)) (.branch 26 (.leaf (-41)) (.leaf (-40))))) (.branch 30 (.branch 28 (.leaf (-39)) (.branch 29 (.leaf (-38)) (.leaf (-37)))) (.branch 31 (.leaf (-36)) (.branch 32 (.leaf (-35)) (.leaf (-34)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (-33)) (.leaf (-32))) (.branch 36 (.leaf (-31)) (.branch 37 (.leaf (-30)) (.leaf (-29))))) (.branch 41 (.branch 39 (.leaf (-28)) (.branch 40 (.leaf (-27)) (.leaf (-26)))) (.branch 42 (.leaf (-25)) (.branch 43 (.leaf (-24)) (.leaf (-23))))))) (.branch 55 (.branch 49 (.branch 46 (.branch 45 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18))))) (.branch 52 (.branch 50 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_289_4925 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (5))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (7))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (6)) (.leaf (0))) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (4))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (8)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (7)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (1)) (.leaf (6))) (.branch 40 (.leaf (0)) (.leaf (4))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (1)) (.leaf (3)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (8))) (.branch 48 (.leaf (1)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (0))) (.branch 52 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (4))) (.branch 56 (.leaf (1)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (7)) (.leaf (0))) (.branch 60 (.leaf (1)) (.leaf (6)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (3))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (0)) (.leaf (8)))))))))
  code := certificateP9_4925
  counts := ![(.branch 32 (.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 26 (.leaf (9)) (.branch 29 (.leaf (10)) (.leaf (11)))))) (.branch 49 (.branch 40 (.branch 34 (.leaf (12)) (.branch 37 (.leaf (13)) (.leaf (14)))) (.branch 43 (.leaf (15)) (.branch 46 (.leaf (16)) (.leaf (17))))) (.branch 57 (.branch 51 (.leaf (18)) (.branch 54 (.leaf (19)) (.leaf (20)))) (.branch 62 (.branch 59 (.leaf (21)) (.leaf (22))) (.branch 65 (.leaf (23)) (.leaf (24))))))),
  (.branch 31 (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 38 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 44 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 47 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 26 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 34 (.leaf (-10)) (.branch 59 (.leaf (-12)) (.leaf (-13))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 11 (.leaf (-16)) (.branch 44 (.leaf (-26)) (.leaf (-35))))),
  (.branch 3 (.leaf (0)) (.leaf (-27))),
  (.branch 12 (.leaf (0)) (.branch 45 (.leaf (-5)) (.leaf (-6)))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (-10))) (.branch 55 (.leaf (-14)) (.leaf (-17)))),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5))),
  (.branch 14 (.leaf (0)) (.branch 33 (.leaf (-10)) (.leaf (-15)))),
  (.branch 47 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 60 (.leaf (-13)) (.branch 63 (.leaf (-12)) (.leaf (-11)))),
  (.branch 53 (.branch 45 (.leaf (-35)) (.branch 49 (.leaf (-34)) (.leaf (-33)))) (.branch 61 (.branch 57 (.leaf (-32)) (.leaf (-31))) (.branch 65 (.leaf (-30)) (.leaf (-24))))),
  (.branch 59 (.branch 55 (.branch 37 (.leaf (-27)) (.branch 54 (.leaf (-26)) (.leaf (-24)))) (.branch 57 (.branch 56 (.leaf (-22)) (.leaf (-20))) (.branch 58 (.leaf (-18)) (.leaf (-16))))) (.branch 62 (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 64 (.branch 46 (.leaf (-6)) (.leaf (-5))) (.branch 65 (.leaf (-4)) (.leaf (-3)))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-17)) (.leaf (-16))) (.branch 58 (.leaf (-15)) (.branch 59 (.leaf (-14)) (.leaf (-13))))) (.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-11)) (.leaf (-10)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7)))))),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 61 (.branch 59 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 60 (.leaf (-13)) (.leaf (-12)))) (.branch 63 (.branch 62 (.leaf (-11)) (.leaf (-10))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7)))))),
  (.branch 48 (.leaf (-1)) (.leaf (0)))]
def witnessP9_289_4926 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (6))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (0))) (.branch 19 (.leaf (2)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (7))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (1)) (.leaf (6))) (.branch 40 (.leaf (0)) (.leaf (4))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (3))) (.branch 48 (.leaf (0)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (0))) (.branch 52 (.leaf (2)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (8))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (4)) (.leaf (0))) (.branch 60 (.leaf (1)) (.leaf (2)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (3))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (0)) (.leaf (5)))))))))
  code := certificateP9_4926
  counts := ![(.branch 32 (.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 26 (.leaf (9)) (.branch 29 (.leaf (10)) (.leaf (11)))))) (.branch 48 (.branch 40 (.branch 34 (.leaf (12)) (.branch 37 (.leaf (13)) (.leaf (14)))) (.branch 43 (.leaf (15)) (.branch 45 (.leaf (16)) (.leaf (17))))) (.branch 56 (.branch 51 (.leaf (18)) (.branch 54 (.leaf (19)) (.leaf (20)))) (.branch 62 (.branch 59 (.leaf (21)) (.leaf (22))) (.branch 65 (.leaf (23)) (.leaf (24))))))),
  (.branch 31 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 28 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 55 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 19 (.leaf (-22)) (.leaf (-23)))),
  (.branch 14 (.leaf (0)) (.branch 30 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-17))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-27))),
  (.branch 22 (.leaf (0)) (.leaf (-44))),
  (.branch 55 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 60 (.branch 57 (.leaf (-7)) (.leaf (-6))) (.branch 63 (.leaf (-5)) (.leaf (-4)))),
  (.branch 61 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 63 (.branch 53 (.leaf (-23)) (.branch 62 (.leaf (-20)) (.leaf (-16)))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 61 (.branch 59 (.branch 42 (.leaf (-17)) (.leaf (-16))) (.branch 60 (.leaf (-14)) (.leaf (-12)))) (.branch 63 (.branch 62 (.leaf (-10)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (0)),
  (.branch 52 (.branch 45 (.branch 42 (.branch 40 (.leaf (-27)) (.branch 41 (.leaf (-26)) (.leaf (-25)))) (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19)))) (.branch 50 (.branch 49 (.leaf (-18)) (.leaf (-17))) (.branch 51 (.leaf (-16)) (.leaf (-15)))))) (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (-44)) (.leaf (-43))) (.branch 25 (.leaf (-42)) (.branch 26 (.leaf (-41)) (.leaf (-40))))) (.branch 30 (.branch 28 (.leaf (-39)) (.branch 29 (.leaf (-38)) (.leaf (-37)))) (.branch 31 (.leaf (-36)) (.branch 32 (.leaf (-35)) (.leaf (-34)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (-33)) (.leaf (-32))) (.branch 36 (.leaf (-31)) (.branch 37 (.leaf (-30)) (.leaf (-29))))) (.branch 41 (.branch 39 (.leaf (-28)) (.branch 40 (.leaf (-27)) (.leaf (-26)))) (.branch 42 (.leaf (-25)) (.branch 43 (.leaf (-24)) (.leaf (-23))))))) (.branch 55 (.branch 49 (.branch 46 (.branch 45 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18))))) (.branch 52 (.branch 50 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_289_4927 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (0))) (.branch 19 (.leaf (1)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (6))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (0)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (3)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (4)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 40 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (3)) (.leaf (0))) (.branch 44 (.leaf (7)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (3)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (5))) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (0))) (.branch 56 (.leaf (3)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (4))) (.branch 60 (.leaf (0)) (.leaf (2)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (3)) (.branch 65 (.leaf (0)) (.leaf (8)))))))))
  code := certificateP9_4927
  counts := ![(.branch 33 (.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 18 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))) (.branch 28 (.branch 26 (.leaf (10)) (.leaf (11))) (.branch 31 (.leaf (12)) (.leaf (13)))))) (.branch 50 (.branch 40 (.branch 36 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16)))) (.branch 45 (.branch 43 (.leaf (17)) (.leaf (18))) (.branch 48 (.leaf (19)) (.leaf (20))))) (.branch 58 (.branch 53 (.leaf (21)) (.branch 55 (.leaf (22)) (.leaf (23)))) (.branch 62 (.branch 60 (.leaf (24)) (.leaf (25))) (.branch 65 (.leaf (26)) (.leaf (27))))))),
  (.branch 30 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 54 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 34 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 37 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1))),
  (.branch 66 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 17 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 15 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 22 (.leaf (0)) (.leaf (-44))),
  (.branch 44 (.leaf (0)) (.leaf (-22))),
  (.leaf (0))]
  high := ![(.branch 63 (.leaf (-14)) (.leaf (-9))),
  (.branch 64 (.branch 58 (.leaf (-7)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 63 (.branch 62 (.leaf (-15)) (.leaf (-12))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.leaf (-8)) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 54 (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 44 (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (-44)) (.leaf (-43))) (.branch 25 (.leaf (-42)) (.branch 26 (.leaf (-41)) (.leaf (-40))))) (.branch 30 (.branch 28 (.leaf (-39)) (.branch 29 (.leaf (-38)) (.leaf (-37)))) (.branch 31 (.leaf (-36)) (.branch 32 (.leaf (-35)) (.leaf (-34)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (-33)) (.leaf (-32))) (.branch 36 (.leaf (-31)) (.branch 37 (.leaf (-30)) (.leaf (-29))))) (.branch 41 (.branch 39 (.leaf (-28)) (.branch 40 (.leaf (-27)) (.leaf (-26)))) (.branch 42 (.leaf (-25)) (.branch 43 (.leaf (-24)) (.leaf (-23))))))) (.branch 55 (.branch 49 (.branch 46 (.branch 45 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18))))) (.branch 52 (.branch 50 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 55 (.branch 49 (.branch 46 (.branch 45 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18))))) (.branch 52 (.branch 50 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_289_4928 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (3)) (.leaf (7)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (6)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (1))) (.branch 23 (.leaf (4)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (5))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (8)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (3)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (6))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (4)) (.leaf (1))) (.branch 44 (.leaf (0)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (3)) (.leaf (7)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (5)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (1))) (.branch 56 (.leaf (4)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (1)) (.leaf (3))) (.branch 60 (.leaf (0)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (6))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (1)) (.leaf (8)))))))))
  code := certificateP9_4928
  counts := ![(.branch 31 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 37 (.branch 34 (.leaf (10)) (.leaf (11))) (.branch 40 (.leaf (12)) (.branch 44 (.leaf (13)) (.leaf (14))))) (.branch 57 (.branch 50 (.leaf (15)) (.branch 53 (.leaf (16)) (.leaf (17)))) (.branch 60 (.leaf (18)) (.branch 64 (.leaf (19)) (.leaf (20))))))),
  (.branch 32 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 51 (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.branch 47 (.leaf (12)) (.leaf (13))))) (.branch 58 (.branch 55 (.leaf (14)) (.leaf (15))) (.branch 61 (.leaf (16)) (.branch 65 (.leaf (17)) (.leaf (18))))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2)))),
  (.branch 33 (.leaf (0)) (.branch 66 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-12)) (.leaf (-14)))) (.branch 40 (.branch 13 (.leaf (-16)) (.leaf (-20))) (.branch 46 (.leaf (-21)) (.leaf (-25))))),
  (.branch 28 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 35 (.leaf (-12)) (.branch 61 (.leaf (-15)) (.leaf (-18))))),
  (.branch 3 (.leaf (0)) (.branch 36 (.leaf (-11)) (.leaf (-13)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-6)) (.leaf (-7)))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (-9))) (.branch 56 (.leaf (-13)) (.leaf (-16)))),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 19 (.leaf (0)) (.leaf (-3))),
  (.branch 16 (.leaf (0)) (.leaf (-17))),
  (.leaf (0))]
  high := ![(.branch 54 (.branch 47 (.leaf (-25)) (.leaf (-24))) (.branch 61 (.leaf (-23)) (.branch 65 (.leaf (-20)) (.leaf (-15))))),
  (.branch 62 (.leaf (-18)) (.leaf (-17))),
  (.branch 63 (.branch 37 (.leaf (-13)) (.leaf (-12))) (.branch 64 (.leaf (-10)) (.branch 65 (.leaf (-8)) (.leaf (-6))))),
  (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 61 (.branch 58 (.branch 57 (.leaf (-16)) (.leaf (-15))) (.branch 59 (.leaf (-14)) (.branch 60 (.leaf (-13)) (.leaf (-12))))) (.branch 63 (.branch 62 (.leaf (-11)) (.leaf (-10))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7)))))),
  (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))) (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.leaf (-10))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_289_4929 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (5))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (7))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (3))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (8)) (.leaf (1))) (.branch 23 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (0))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (7)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (3)) (.leaf (6))) (.branch 40 (.leaf (4)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (8))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (5)) (.leaf (3))) (.branch 48 (.leaf (1)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (4)) (.leaf (6))) (.branch 52 (.leaf (2)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (7)) (.leaf (1))) (.branch 56 (.leaf (3)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (5)) (.leaf (0))) (.branch 60 (.leaf (2)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (4)) (.leaf (0))) (.branch 64 (.leaf (3)) (.branch 65 (.leaf (8)) (.leaf (6)))))))))
  code := certificateP9_4929
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 66 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 43 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 26 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-14)) (.leaf (-18)))) (.branch 37 (.leaf (-22)) (.branch 59 (.leaf (-24)) (.leaf (-28))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-23))) (.branch 28 (.leaf (-24)) (.leaf (-25)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 19 (.leaf (-22)) (.branch 27 (.leaf (-23)) (.leaf (-24))))),
  (.branch 5 (.leaf (0)) (.branch 38 (.leaf (-7)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-4)) (.leaf (-5)))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (-8))) (.branch 58 (.leaf (-10)) (.leaf (-12)))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (-1))) (.branch 51 (.leaf (-3)) (.leaf (-5)))),
  (.branch 10 (.leaf (0)) (.leaf (-12))),
  (.branch 21 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 64 (.branch 60 (.leaf (-28)) (.leaf (-27))) (.branch 65 (.leaf (-22)) (.leaf (-17)))),
  (.branch 63 (.branch 62 (.leaf (-25)) (.leaf (-20))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-10)) (.leaf (-5))))),
  (.branch 63 (.branch 61 (.leaf (-24)) (.branch 62 (.leaf (-20)) (.leaf (-16)))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 39 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-6)))),
  (.branch 63 (.branch 51 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-11))) (.branch 61 (.leaf (-10)) (.leaf (-9)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-5))))),
  (.branch 54 (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))) (.branch 55 (.leaf (-2)) (.branch 56 (.leaf (-1)) (.leaf (0))))),
  (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_289_4930 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (8)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (6)) (.leaf (0))) (.branch 19 (.leaf (4)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (7))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (6)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (5)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (4)) (.leaf (6))) (.branch 40 (.leaf (8)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (3)) (.leaf (5))) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (4))) (.branch 48 (.leaf (0)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (6)) (.leaf (0))) (.branch 52 (.leaf (3)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (5)) (.leaf (0))) (.branch 56 (.leaf (4)) (.leaf (7))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (2)) (.leaf (0))) (.branch 60 (.leaf (1)) (.leaf (3)))) (.branch 63 (.branch 62 (.leaf (6)) (.leaf (0))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (5)) (.leaf (4)))))))))
  code := certificateP9_4930
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 55 (.branch 51 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 27 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 36 (.leaf (5)) (.branch 46 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.leaf (7))))),
  (.branch 38 (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 47 (.leaf (4)) (.leaf (5))) (.branch 66 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.leaf (0)) (.branch 57 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))) (.branch 18 (.leaf (-15)) (.branch 51 (.leaf (-18)) (.leaf (-21))))),
  (.branch 27 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 35 (.leaf (-14)) (.branch 60 (.leaf (-15)) (.leaf (-16))))),
  (.branch 31 (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-6)) (.leaf (-11)))) (.branch 49 (.branch 36 (.leaf (-14)) (.leaf (-18))) (.branch 64 (.leaf (-23)) (.leaf (-26))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (-31))) (.branch 23 (.leaf (-34)) (.leaf (-37)))),
  (.branch 9 (.leaf (0)) (.branch 56 (.leaf (-3)) (.leaf (-4)))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 24 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-26)))]
  high := ![(.branch 60 (.branch 52 (.leaf (-21)) (.branch 56 (.leaf (-20)) (.leaf (-19)))) (.branch 64 (.leaf (-18)) (.branch 65 (.leaf (-14)) (.leaf (-10))))),
  (.branch 63 (.branch 61 (.leaf (-16)) (.branch 62 (.leaf (-14)) (.leaf (-12)))) (.branch 64 (.leaf (-10)) (.branch 65 (.leaf (-8)) (.leaf (-6))))),
  (.branch 65 (.leaf (-26)) (.leaf (-25))),
  (.branch 62 (.branch 24 (.leaf (-37)) (.branch 43 (.leaf (-36)) (.leaf (-35)))) (.branch 64 (.branch 63 (.leaf (-28)) (.leaf (-21))) (.branch 65 (.leaf (-14)) (.leaf (-7))))),
  (.branch 57 (.leaf (-4)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 63 (.branch 51 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.branch 46 (.branch 43 (.branch 41 (.leaf (-26)) (.branch 42 (.leaf (-25)) (.leaf (-24)))) (.branch 44 (.leaf (-23)) (.branch 45 (.leaf (-22)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18)))) (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))))) (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_289_4931 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (6))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (4)) (.leaf (0))) (.branch 40 (.leaf (2)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (3))) (.branch 44 (.leaf (7)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (4)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (3))) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (5))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (3)) (.leaf (0))) (.branch 60 (.leaf (4)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (3)) (.leaf (8)))))))))
  code := certificateP9_4931
  counts := ![(.branch 31 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 26 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))) (.branch 48 (.branch 39 (.branch 34 (.leaf (12)) (.branch 37 (.leaf (13)) (.leaf (14)))) (.branch 42 (.leaf (15)) (.branch 45 (.leaf (16)) (.leaf (17))))) (.branch 56 (.branch 50 (.leaf (18)) (.branch 53 (.leaf (19)) (.leaf (20)))) (.branch 61 (.branch 59 (.leaf (21)) (.leaf (22))) (.branch 64 (.leaf (23)) (.leaf (24))))))),
  (.branch 30 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 54 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1))),
  (.branch 66 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.branch 22 (.leaf (0)) (.leaf (-44))),
  (.branch 44 (.leaf (0)) (.leaf (-22))),
  (.leaf (0))]
  high := ![(.branch 62 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.branch 64 (.branch 58 (.leaf (-7)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 63 (.branch 55 (.leaf (-14)) (.leaf (-12))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 44 (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (-44)) (.leaf (-43))) (.branch 25 (.leaf (-42)) (.branch 26 (.leaf (-41)) (.leaf (-40))))) (.branch 30 (.branch 28 (.leaf (-39)) (.branch 29 (.leaf (-38)) (.leaf (-37)))) (.branch 31 (.leaf (-36)) (.branch 32 (.leaf (-35)) (.leaf (-34)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (-33)) (.leaf (-32))) (.branch 36 (.leaf (-31)) (.branch 37 (.leaf (-30)) (.leaf (-29))))) (.branch 41 (.branch 39 (.leaf (-28)) (.branch 40 (.leaf (-27)) (.leaf (-26)))) (.branch 42 (.leaf (-25)) (.branch 43 (.leaf (-24)) (.leaf (-23))))))) (.branch 55 (.branch 49 (.branch 46 (.branch 45 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18))))) (.branch 52 (.branch 50 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 55 (.branch 49 (.branch 46 (.branch 45 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18))))) (.branch 52 (.branch 50 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_289_4932 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (6)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (7))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (8)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (5)) (.leaf (0))) (.branch 40 (.leaf (2)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (3))) (.branch 44 (.leaf (6)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (4)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (3))) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (7))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (3)) (.leaf (0))) (.branch 60 (.leaf (5)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (3)) (.leaf (8)))))))))
  code := certificateP9_4932
  counts := ![(.branch 31 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 26 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))) (.branch 48 (.branch 39 (.branch 34 (.leaf (12)) (.branch 37 (.leaf (13)) (.leaf (14)))) (.branch 42 (.leaf (15)) (.branch 45 (.leaf (16)) (.leaf (17))))) (.branch 56 (.branch 50 (.leaf (18)) (.branch 53 (.leaf (19)) (.leaf (20)))) (.branch 61 (.branch 59 (.leaf (21)) (.leaf (22))) (.branch 64 (.leaf (23)) (.leaf (24))))))),
  (.branch 30 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 54 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2)))),
  (.branch 33 (.leaf (0)) (.branch 66 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 16 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.leaf (-22))),
  (.branch 22 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 62 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.branch 64 (.branch 58 (.leaf (-7)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 63 (.branch 55 (.leaf (-14)) (.leaf (-12))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))) (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.leaf (-10))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 49 (.branch 46 (.branch 45 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18))))) (.branch 52 (.branch 50 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))))) (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_289_4933 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (7)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (8))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (5)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (6))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (4)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (1)) (.leaf (0))) (.branch 52 (.leaf (7)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (3))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (2)) (.leaf (0))) (.branch 60 (.leaf (5)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (8))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (1)) (.leaf (3)))))))))
  code := certificateP9_4933
  counts := ![(.branch 31 (.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 18 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 26 (.leaf (9)) (.branch 29 (.leaf (10)) (.leaf (11)))))) (.branch 48 (.branch 40 (.branch 34 (.leaf (12)) (.branch 37 (.leaf (13)) (.leaf (14)))) (.branch 42 (.leaf (15)) (.branch 45 (.leaf (16)) (.leaf (17))))) (.branch 56 (.branch 51 (.leaf (18)) (.branch 53 (.leaf (19)) (.leaf (20)))) (.branch 62 (.branch 59 (.leaf (21)) (.leaf (22))) (.branch 64 (.leaf (23)) (.leaf (24))))))),
  (.branch 32 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 50 (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 54 (.leaf (14)) (.leaf (15))) (.branch 61 (.leaf (16)) (.branch 65 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.branch 63 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 16 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-25))),
  (.branch 19 (.leaf (0)) (.leaf (-14))),
  (.branch 30 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 65 (.leaf (-8)) (.leaf (-4))),
  (.branch 58 (.leaf (-5)) (.branch 62 (.leaf (-4)) (.leaf (-3)))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))) (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.leaf (-10))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 47 (.branch 44 (.branch 42 (.leaf (-25)) (.branch 43 (.leaf (-24)) (.leaf (-23)))) (.branch 45 (.leaf (-22)) (.branch 46 (.leaf (-21)) (.leaf (-20))))) (.branch 50 (.branch 48 (.leaf (-19)) (.branch 49 (.leaf (-18)) (.leaf (-17)))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-15)) (.leaf (-14)))))) (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_289_4934 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (7))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (5))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (8)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (7)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (6)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (4)) (.leaf (8))) (.branch 40 (.leaf (1)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (5))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (6)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (7)) (.leaf (1))) (.branch 52 (.leaf (0)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (4)) (.leaf (3))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (2)) (.leaf (0))) (.branch 60 (.leaf (5)) (.leaf (8)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (0))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (6)) (.leaf (3)))))))))
  code := certificateP9_4934
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (-23)) (.leaf (-24)))),
  (.branch 10 (.leaf (0)) (.leaf (-13))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 64 (.branch 60 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 59 (.leaf (-5)) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 60 (.branch 57 (.branch 55 (.leaf (-24)) (.branch 56 (.leaf (-22)) (.leaf (-20)))) (.branch 58 (.leaf (-18)) (.branch 59 (.leaf (-16)) (.leaf (-14))))) (.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-10)) (.leaf (-8)))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 62 (.branch 44 (.leaf (-13)) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_289_4935 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (0))) (.branch 19 (.leaf (3)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (5))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (6))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (8)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (5)) (.leaf (4))) (.branch 40 (.leaf (1)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (6)) (.leaf (2))) (.branch 44 (.leaf (0)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (0))) (.branch 48 (.leaf (1)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (7)) (.leaf (0))) (.branch 52 (.leaf (4)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (5))) (.branch 56 (.leaf (2)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (1)) (.leaf (6))) (.branch 60 (.leaf (3)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (4)) (.leaf (8)))))))))
  code := certificateP9_4935
  counts := ![(.branch 31 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))))) (.branch 47 (.branch 37 (.branch 34 (.leaf (10)) (.leaf (11))) (.branch 41 (.leaf (12)) (.branch 44 (.leaf (13)) (.leaf (14))))) (.branch 57 (.branch 51 (.leaf (15)) (.branch 54 (.leaf (16)) (.leaf (17)))) (.branch 61 (.leaf (18)) (.branch 64 (.leaf (19)) (.leaf (20))))))),
  (.branch 30 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 48 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 36 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 65 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 33 (.leaf (0)) (.branch 66 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-23)) (.leaf (-26)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 48 (.leaf (-26)) (.leaf (-31)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-18))) (.branch 29 (.leaf (-19)) (.leaf (-20)))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (-15))) (.branch 32 (.leaf (-16)) (.leaf (-17)))),
  (.branch 39 (.branch 13 (.leaf (0)) (.leaf (-1))) (.branch 52 (.leaf (-3)) (.branch 65 (.leaf (-4)) (.leaf (-5))))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 17 (.leaf (0)) (.leaf (-16))),
  (.leaf (0))]
  high := ![(.branch 48 (.branch 38 (.leaf (-26)) (.leaf (-25))) (.branch 58 (.leaf (-24)) (.branch 65 (.leaf (-20)) (.leaf (-10))))),
  (.branch 59 (.branch 49 (.leaf (-31)) (.branch 54 (.leaf (-30)) (.leaf (-29)))) (.branch 64 (.leaf (-28)) (.branch 65 (.leaf (-22)) (.leaf (-16))))),
  (.branch 64 (.branch 63 (.leaf (-20)) (.leaf (-15))) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.branch 47 (.branch 33 (.leaf (-17)) (.leaf (-16))) (.branch 61 (.leaf (-15)) (.leaf (-13)))) (.branch 64 (.branch 63 (.leaf (-11)) (.leaf (-9))) (.branch 65 (.leaf (-7)) (.leaf (-5))))),
  (.leaf (-5)),
  (.branch 60 (.branch 57 (.branch 39 (.leaf (-23)) (.branch 56 (.leaf (-22)) (.leaf (-20)))) (.branch 58 (.leaf (-18)) (.branch 59 (.leaf (-16)) (.leaf (-14))))) (.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-10)) (.leaf (-8)))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 62 (.branch 60 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_289_4936 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (7)) (.leaf (3))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (6)) (.leaf (1))) (.branch 40 (.leaf (4)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (1))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (5)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (4)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (8)) (.leaf (3))) (.branch 56 (.leaf (1)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (2)) (.leaf (0))) (.branch 60 (.leaf (1)) (.leaf (4)))) (.branch 63 (.branch 62 (.leaf (5)) (.leaf (0))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (1)) (.leaf (3)))))))))
  code := certificateP9_4936
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 32 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 51 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 26 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-14)) (.leaf (-18)))) (.branch 37 (.leaf (-22)) (.branch 59 (.leaf (-24)) (.leaf (-28))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.branch 14 (.leaf (-9)) (.leaf (-10))))) (.branch 43 (.branch 35 (.leaf (-11)) (.branch 39 (.leaf (-12)) (.leaf (-13)))) (.branch 47 (.leaf (-14)) (.branch 51 (.leaf (-15)) (.leaf (-16)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 52 (.leaf (-17)) (.leaf (-20)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-4)) (.leaf (-5)))),
  (.branch 13 (.leaf (0)) (.branch 29 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-28))),
  (.branch 21 (.leaf (0)) (.leaf (-45))),
  (.branch 54 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 64 (.branch 60 (.leaf (-28)) (.leaf (-27))) (.branch 65 (.leaf (-22)) (.leaf (-17)))),
  (.branch 52 (.leaf (-16)) (.branch 61 (.leaf (-15)) (.leaf (-13)))),
  (.branch 59 (.branch 53 (.leaf (-20)) (.leaf (-18))) (.branch 65 (.leaf (-16)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 45 (.branch 41 (.branch 39 (.leaf (-28)) (.branch 40 (.leaf (-27)) (.leaf (-26)))) (.branch 43 (.branch 42 (.leaf (-25)) (.leaf (-24))) (.branch 44 (.leaf (-23)) (.leaf (-22))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19)))) (.branch 50 (.branch 49 (.leaf (-18)) (.leaf (-17))) (.branch 51 (.leaf (-16)) (.leaf (-15)))))) (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (-45)) (.leaf (-44))) (.branch 24 (.leaf (-43)) (.branch 25 (.leaf (-42)) (.leaf (-41))))) (.branch 29 (.branch 27 (.leaf (-40)) (.branch 28 (.leaf (-39)) (.leaf (-38)))) (.branch 30 (.leaf (-37)) (.branch 31 (.leaf (-36)) (.leaf (-35)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (-34)) (.leaf (-33))) (.branch 35 (.leaf (-32)) (.branch 36 (.leaf (-31)) (.leaf (-30))))) (.branch 40 (.branch 38 (.leaf (-29)) (.branch 39 (.leaf (-28)) (.leaf (-27)))) (.branch 41 (.leaf (-26)) (.branch 42 (.leaf (-25)) (.leaf (-24))))))) (.branch 54 (.branch 48 (.branch 45 (.branch 44 (.leaf (-23)) (.leaf (-22))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19))))) (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_289_4937 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (8)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (6))) (.branch 23 (.leaf (1)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (7)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (2))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (8)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (3))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (0))) (.branch 44 (.leaf (6)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (4)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (7)) (.leaf (1))) (.branch 52 (.leaf (0)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (5))) (.branch 56 (.leaf (1)) (.leaf (3))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (2))) (.branch 60 (.leaf (0)) (.leaf (8)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (2))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (4)) (.leaf (6)))))))))
  code := certificateP9_4937
  counts := ![(.branch 31 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))) (.branch 48 (.branch 40 (.branch 34 (.leaf (11)) (.branch 37 (.leaf (12)) (.leaf (13)))) (.branch 43 (.leaf (14)) (.branch 46 (.leaf (15)) (.leaf (16))))) (.branch 58 (.branch 52 (.leaf (17)) (.branch 54 (.leaf (18)) (.leaf (19)))) (.branch 60 (.leaf (20)) (.branch 64 (.leaf (21)) (.leaf (22))))))),
  (.branch 29 (.branch 12 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-18))) (.branch 39 (.leaf (-26)) (.leaf (-29)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 30 (.leaf (-14)) (.branch 63 (.leaf (-18)) (.leaf (-21))))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (-17)) (.leaf (-18)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (-1)) (.leaf (-2)))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 17 (.leaf (0)) (.branch 38 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 61 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 63 (.branch 40 (.leaf (-29)) (.branch 57 (.leaf (-28)) (.leaf (-26)))) (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-16)) (.leaf (-11))))),
  (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-16)) (.leaf (-11)))),
  (.branch 61 (.branch 59 (.branch 58 (.leaf (-18)) (.leaf (-16))) (.branch 60 (.leaf (-14)) (.leaf (-12)))) (.branch 63 (.branch 62 (.leaf (-10)) (.leaf (-8))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (-2)),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 57 (.branch 53 (.branch 51 (.branch 6 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))) (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.leaf (-10))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.branch 39 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_289_4938 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (1))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (6)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (8)) (.leaf (3))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (7)) (.leaf (1))) (.branch 40 (.leaf (6)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (1))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (4)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (8)) (.leaf (3))) (.branch 56 (.leaf (1)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (2)) (.leaf (0))) (.branch 60 (.leaf (1)) (.leaf (6)))) (.branch 63 (.branch 62 (.leaf (4)) (.leaf (0))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (1)) (.leaf (3)))))))))
  code := certificateP9_4938
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 32 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 51 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 26 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-14)) (.leaf (-18)))) (.branch 37 (.leaf (-22)) (.branch 59 (.leaf (-24)) (.leaf (-28))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.branch 14 (.leaf (-9)) (.leaf (-10))))) (.branch 43 (.branch 35 (.leaf (-11)) (.branch 39 (.leaf (-12)) (.leaf (-13)))) (.branch 47 (.leaf (-14)) (.branch 51 (.leaf (-15)) (.leaf (-16)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 52 (.leaf (-17)) (.leaf (-20)))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.branch 29 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 28 (.leaf (-15)) (.leaf (-16)))),
  (.branch 17 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-28))),
  (.branch 21 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 64 (.branch 60 (.leaf (-28)) (.leaf (-27))) (.branch 65 (.leaf (-22)) (.leaf (-17)))),
  (.branch 52 (.leaf (-16)) (.branch 61 (.leaf (-15)) (.leaf (-13)))),
  (.branch 59 (.branch 53 (.leaf (-20)) (.leaf (-18))) (.branch 65 (.leaf (-16)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.branch 45 (.branch 41 (.branch 39 (.leaf (-28)) (.branch 40 (.leaf (-27)) (.leaf (-26)))) (.branch 43 (.branch 42 (.leaf (-25)) (.leaf (-24))) (.branch 44 (.leaf (-23)) (.leaf (-22))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19)))) (.branch 50 (.branch 49 (.leaf (-18)) (.leaf (-17))) (.branch 51 (.leaf (-16)) (.leaf (-15)))))) (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_289_4939 : CycleWitness 9 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (7)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (8)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (6))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (7)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (8)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (1))) (.branch 44 (.leaf (6)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (4)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (7)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (5))) (.branch 56 (.leaf (1)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (2)) (.leaf (0))) (.branch 60 (.leaf (1)) (.leaf (4)))) (.branch 63 (.branch 62 (.leaf (8)) (.leaf (0))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (1)) (.leaf (6)))))))))
  code := certificateP9_4939
  counts := ![(.branch 30 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 32 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 51 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 26 (.leaf (-13)) (.branch 59 (.leaf (-16)) (.leaf (-19))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.branch 14 (.leaf (-9)) (.leaf (-10))))) (.branch 43 (.branch 35 (.leaf (-11)) (.branch 39 (.leaf (-12)) (.leaf (-13)))) (.branch 47 (.leaf (-14)) (.branch 51 (.leaf (-15)) (.leaf (-16)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 52 (.leaf (-17)) (.leaf (-20)))),
  (.branch 4 (.leaf (0)) (.leaf (-25))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (-4))) (.branch 61 (.leaf (-6)) (.leaf (-7)))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 50 (.leaf (-15)) (.leaf (-16)))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 64 (.branch 60 (.leaf (-19)) (.leaf (-18))) (.branch 65 (.leaf (-14)) (.leaf (-10)))),
  (.branch 52 (.leaf (-16)) (.branch 61 (.leaf (-15)) (.leaf (-13)))),
  (.branch 59 (.branch 53 (.leaf (-20)) (.leaf (-18))) (.branch 65 (.leaf (-16)) (.leaf (-11)))),
  (.branch 59 (.branch 56 (.branch 38 (.leaf (-25)) (.branch 55 (.leaf (-24)) (.leaf (-22)))) (.branch 57 (.leaf (-20)) (.branch 58 (.leaf (-18)) (.leaf (-16))))) (.branch 62 (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 63 (.branch 62 (.leaf (-7)) (.leaf (-6))) (.branch 64 (.leaf (-5)) (.branch 65 (.leaf (-4)) (.leaf (-3))))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_289 : Fin 45 → CycleWitness 9 := ![witnessP9_289_4895, witnessP9_289_4896, witnessP9_289_4897, witnessP9_289_4898, witnessP9_289_4899, witnessP9_289_4900, witnessP9_289_4901, witnessP9_289_4902, witnessP9_289_4903, witnessP9_289_4904, witnessP9_289_4905, witnessP9_289_4906, witnessP9_289_4907, witnessP9_289_4908, witnessP9_289_4909, witnessP9_289_4910, witnessP9_289_4911, witnessP9_289_4912, witnessP9_289_4913, witnessP9_289_4914, witnessP9_289_4915, witnessP9_289_4916, witnessP9_289_4917, witnessP9_289_4918, witnessP9_289_4919, witnessP9_289_4920, witnessP9_289_4921, witnessP9_289_4922, witnessP9_289_4923, witnessP9_289_4924, witnessP9_289_4925, witnessP9_289_4926, witnessP9_289_4927, witnessP9_289_4928, witnessP9_289_4929, witnessP9_289_4930, witnessP9_289_4931, witnessP9_289_4932, witnessP9_289_4933, witnessP9_289_4934, witnessP9_289_4935, witnessP9_289_4936, witnessP9_289_4937, witnessP9_289_4938, witnessP9_289_4939]
end RealPinwheel.FiveSixths


