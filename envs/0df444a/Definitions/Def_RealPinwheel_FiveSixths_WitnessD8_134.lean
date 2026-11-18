-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_134
-- name    : RealPinwheel_FiveSixths_WitnessD8_134
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:54:38.986099+00:00
-- url     : https://prove2.me/theorems/2307ffc3-5be6-4653-ad37-d0734f53ddc6
-- title:
--   Exact witness block D8_134
-- statement:
--   These exact witnesses represent words 1074 through 1087 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1074–1087; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_134_1073 : CycleWitness 8 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (7)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (5))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (3))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (6)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (7)) (.branch 25 (.leaf (1)) (.leaf (0)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (5))) (.branch 29 (.leaf (3)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (6))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (4)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (7)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (3))) (.branch 42 (.leaf (5)) (.leaf (1))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (2))) (.branch 46 (.leaf (6)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (4))) (.branch 50 (.leaf (2)) (.branch 51 (.leaf (0)) (.leaf (3))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (7)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (5)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (6)) (.branch 60 (.leaf (1)) (.leaf (0)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (2)) (.leaf (4))) (.branch 64 (.leaf (3)) (.leaf (0)))) (.branch 67 (.branch 66 (.leaf (1)) (.leaf (7))) (.branch 68 (.leaf (0)) (.branch 69 (.leaf (2)) (.leaf (5)))))))))
  code := certificateD8_1073
  counts := ![(.branch 33 (.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))) (.branch 51 (.branch 40 (.branch 36 (.leaf (10)) (.leaf (11))) (.branch 44 (.leaf (12)) (.branch 47 (.leaf (13)) (.leaf (14))))) (.branch 61 (.branch 55 (.leaf (15)) (.branch 58 (.leaf (16)) (.leaf (17)))) (.branch 65 (.leaf (18)) (.branch 68 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 38 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 57 (.leaf (9)) (.leaf (10))) (.branch 69 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 42 (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 56 (.leaf (3)) (.branch 70 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 53 (.leaf (3)) (.branch 67 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 33 (.branch 1 (.leaf (0)) (.branch 26 (.leaf (-13)) (.leaf (-14)))) (.branch 61 (.branch 36 (.leaf (-15)) (.leaf (-18))) (.branch 68 (.leaf (-19)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-23)) (.leaf (-27)))),
  (.branch 3 (.leaf (0)) (.branch 38 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-17)) (.leaf (-19)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 59 (.leaf (-10)) (.leaf (-11)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 69 (.leaf (-20)) (.leaf (-15))),
  (.branch 61 (.branch 49 (.leaf (-27)) (.branch 55 (.leaf (-26)) (.leaf (-25)))) (.branch 68 (.branch 67 (.leaf (-24)) (.leaf (-18))) (.branch 69 (.leaf (-12)) (.leaf (-6))))),
  (.branch 63 (.leaf (-4)) (.leaf (-3))),
  (.branch 66 (.branch 53 (.leaf (-19)) (.branch 65 (.leaf (-18)) (.leaf (-15)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-9))) (.branch 69 (.leaf (-6)) (.leaf (-3))))),
  (.branch 66 (.branch 64 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 64 (.branch 61 (.branch 60 (.leaf (-11)) (.leaf (-10))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-8)) (.leaf (-7))))) (.branch 67 (.branch 65 (.leaf (-6)) (.branch 66 (.leaf (-5)) (.leaf (-4)))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 68 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_134_1074 : CycleWitness 8 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (7)) (.leaf (1))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (5)) (.leaf (0))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (3))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (1)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (5)) (.leaf (3)))) (.branch 32 (.branch 31 (.leaf (7)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (4)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (3)) (.leaf (6)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (5))) (.branch 42 (.leaf (2)) (.leaf (1))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (4))) (.branch 46 (.leaf (3)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (7)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 51 (.leaf (5)) (.leaf (0))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (3))) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (6)) (.leaf (2))) (.branch 59 (.leaf (0)) (.branch 60 (.leaf (4)) (.leaf (1)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (3)) (.leaf (0))) (.branch 64 (.leaf (5)) (.leaf (2)))) (.branch 67 (.branch 66 (.leaf (7)) (.leaf (1))) (.branch 68 (.leaf (0)) (.branch 69 (.leaf (3)) (.leaf (4)))))))))
  code := certificateD8_1074
  counts := ![(.branch 33 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 52 (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.branch 47 (.leaf (12)) (.leaf (13))))) (.branch 59 (.branch 56 (.leaf (14)) (.leaf (15))) (.branch 63 (.leaf (16)) (.branch 68 (.leaf (17)) (.leaf (18))))))),
  (.branch 32 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 61 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 67 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 38 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 46 (.leaf (5)) (.leaf (6))) (.branch 62 (.leaf (7)) (.branch 69 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.branch 70 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 47 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-23))),
  (.branch 34 (.branch 3 (.leaf (0)) (.leaf (-43))) (.branch 65 (.leaf (-44)) (.leaf (-45)))),
  (.branch 7 (.leaf (0)) (.branch 30 (.leaf (-7)) (.leaf (-10)))),
  (.branch 25 (.branch 18 (.leaf (0)) (.leaf (-2))) (.branch 53 (.leaf (-7)) (.branch 60 (.leaf (-8)) (.leaf (-13))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (-6))) (.branch 51 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-27))),
  (.branch 13 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 64 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-3)))),
  (.branch 56 (.branch 44 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 50 (.leaf (-21)) (.leaf (-20)))) (.branch 68 (.branch 62 (.leaf (-19)) (.leaf (-18))) (.branch 69 (.leaf (-12)) (.leaf (-6))))),
  (.branch 67 (.branch 66 (.leaf (-45)) (.leaf (-36))) (.branch 68 (.leaf (-27)) (.branch 69 (.leaf (-18)) (.leaf (-9))))),
  (.branch 31 (.leaf (-10)) (.leaf (-9))),
  (.branch 64 (.branch 62 (.branch 61 (.leaf (-13)) (.leaf (-11))) (.branch 63 (.leaf (-9)) (.leaf (-7)))) (.branch 66 (.branch 65 (.leaf (-5)) (.leaf (-3))) (.branch 67 (.leaf (-1)) (.leaf (0))))),
  (.branch 66 (.branch 52 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7)))) (.branch 68 (.branch 67 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3))))),
  (.branch 63 (.branch 59 (.branch 40 (.leaf (-27)) (.branch 58 (.leaf (-26)) (.leaf (-24)))) (.branch 61 (.branch 60 (.leaf (-22)) (.leaf (-20))) (.branch 62 (.leaf (-18)) (.leaf (-16))))) (.branch 66 (.branch 64 (.leaf (-14)) (.branch 65 (.leaf (-12)) (.leaf (-10)))) (.branch 68 (.branch 67 (.leaf (-8)) (.leaf (-6))) (.branch 69 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 67 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2)))))]
def witnessD8_134_1075 : CycleWitness 8 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (6))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (3))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (3))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (1)) (.leaf (0)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (5)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (6)))) (.branch 32 (.branch 31 (.leaf (3)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (4)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (3)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (7))) (.branch 42 (.leaf (1)) (.leaf (0))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (5)) (.leaf (3))) (.branch 46 (.leaf (2)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (4)) (.leaf (1))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (2)) (.leaf (3))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (6)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (4)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (3)) (.branch 60 (.leaf (1)) (.leaf (0)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (5)) (.leaf (2))) (.branch 64 (.leaf (0)) (.leaf (7)))) (.branch 67 (.branch 66 (.leaf (3)) (.leaf (1))) (.branch 68 (.leaf (0)) (.branch 69 (.leaf (2)) (.leaf (4)))))))))
  code := certificateD8_1075
  counts := ![(.branch 33 (.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))) (.branch 50 (.branch 39 (.branch 36 (.leaf (10)) (.leaf (11))) (.branch 43 (.leaf (12)) (.branch 47 (.leaf (13)) (.leaf (14))))) (.branch 61 (.branch 54 (.leaf (15)) (.branch 57 (.leaf (16)) (.leaf (17)))) (.branch 64 (.leaf (18)) (.branch 68 (.leaf (19)) (.leaf (20))))))),
  (.branch 32 (.branch 14 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 67 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))) (.branch 63 (.branch 58 (.leaf (9)) (.leaf (10))) (.branch 69 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 38 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 59 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 35 (.branch 13 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 48 (.leaf (3)) (.leaf (4))) (.branch 70 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 42 (.leaf (-5)) (.leaf (-6)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 51 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 21 (.leaf (0)) (.branch 56 (.leaf (-5)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 6 (.leaf (0)) (.leaf (-52))),
  (.branch 18 (.leaf (0)) (.branch 41 (.leaf (-16)) (.leaf (-17))))]
  high := ![(.branch 65 (.branch 40 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-2)))),
  (.branch 68 (.branch 61 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1)))),
  (.branch 61 (.branch 58 (.branch 57 (.leaf (-9)) (.leaf (-8))) (.branch 59 (.leaf (-7)) (.branch 60 (.leaf (-6)) (.leaf (-5))))) (.branch 63 (.branch 62 (.leaf (-4)) (.leaf (-3))) (.branch 64 (.leaf (-2)) (.branch 65 (.leaf (-1)) (.leaf (0)))))),
  (.branch 65 (.branch 63 (.branch 45 (.leaf (-17)) (.leaf (-16))) (.branch 64 (.leaf (-14)) (.leaf (-12)))) (.branch 67 (.branch 66 (.leaf (-10)) (.leaf (-8))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 61 (.branch 56 (.branch 54 (.branch 7 (.leaf (-52)) (.leaf (-51))) (.branch 55 (.leaf (-48)) (.leaf (-45)))) (.branch 58 (.branch 57 (.leaf (-42)) (.leaf (-39))) (.branch 59 (.leaf (-36)) (.branch 60 (.leaf (-33)) (.leaf (-30)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (-27)) (.leaf (-24))) (.branch 64 (.leaf (-21)) (.leaf (-18)))) (.branch 67 (.branch 66 (.leaf (-15)) (.leaf (-12))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 67 (.branch 42 (.leaf (-17)) (.branch 66 (.leaf (-15)) (.leaf (-12)))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3)))))]
def witnessD8_134_1076 : CycleWitness 8 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (2)) (.leaf (0))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (7))) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (1)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (6)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (1)) (.leaf (5)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (3)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (7))) (.branch 42 (.leaf (1)) (.leaf (4))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (2))) (.branch 46 (.leaf (1)) (.leaf (3)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (5)) (.branch 51 (.leaf (2)) (.leaf (0))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (6))) (.branch 55 (.leaf (0)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (1))) (.branch 59 (.leaf (0)) (.branch 60 (.leaf (4)) (.leaf (1)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (2)) (.leaf (0))) (.branch 64 (.leaf (3)) (.leaf (1)))) (.branch 67 (.branch 66 (.leaf (7)) (.leaf (0))) (.branch 68 (.leaf (2)) (.branch 69 (.leaf (1)) (.leaf (5)))))))))
  code := certificateD8_1076
  counts := ![(.branch 32 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 52 (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.branch 48 (.leaf (12)) (.leaf (13))))) (.branch 59 (.branch 55 (.leaf (14)) (.leaf (15))) (.branch 63 (.leaf (16)) (.branch 67 (.leaf (17)) (.leaf (18))))))),
  (.branch 34 (.branch 14 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))) (.branch 53 (.branch 42 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.branch 49 (.leaf (12)) (.leaf (13))))) (.branch 61 (.branch 58 (.leaf (14)) (.leaf (15))) (.branch 65 (.leaf (16)) (.branch 69 (.leaf (17)) (.leaf (18))))))),
  (.branch 33 (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 57 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 35 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 70 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-26)) (.leaf (-30)))),
  (.branch 2 (.leaf (0)) (.branch 37 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-11)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-23)) (.leaf (-24)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-19)) (.leaf (-20)))),
  (.branch 15 (.leaf (0)) (.branch 50 (.leaf (-4)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-18))),
  (.branch 19 (.leaf (0)) (.branch 41 (.leaf (-5)) (.leaf (-7))))]
  high := ![(.branch 64 (.branch 56 (.leaf (-30)) (.branch 60 (.leaf (-29)) (.leaf (-28)))) (.branch 68 (.leaf (-27)) (.branch 69 (.leaf (-18)) (.leaf (-9))))),
  (.leaf (-3)),
  (.branch 63 (.leaf (-13)) (.branch 69 (.leaf (-12)) (.leaf (-6)))),
  (.branch 67 (.branch 65 (.leaf (-24)) (.branch 66 (.leaf (-20)) (.leaf (-16)))) (.branch 68 (.leaf (-12)) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 65 (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-18))) (.branch 63 (.leaf (-16)) (.branch 64 (.leaf (-14)) (.leaf (-12))))) (.branch 67 (.branch 66 (.leaf (-10)) (.leaf (-8))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 54 (.branch 52 (.branch 51 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.branch 55 (.leaf (-3)) (.leaf (-2))) (.branch 57 (.leaf (-1)) (.leaf (0))))),
  (.branch 62 (.branch 58 (.branch 56 (.branch 55 (.leaf (-18)) (.leaf (-17))) (.branch 57 (.leaf (-16)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-14)) (.leaf (-13))) (.branch 61 (.leaf (-12)) (.leaf (-11))))) (.branch 66 (.branch 64 (.branch 63 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-8)) (.leaf (-7)))) (.branch 68 (.branch 67 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 67 (.branch 42 (.leaf (-7)) (.leaf (-6))) (.branch 68 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-3)))))]
def witnessD8_134_1077 : CycleWitness 8 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (7))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (6))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (1))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (7)) (.branch 25 (.leaf (1)) (.leaf (0)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (3)) (.leaf (6))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (4))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (5)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (3)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (7))) (.branch 42 (.leaf (6)) (.leaf (1))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (4))) (.branch 46 (.leaf (1)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (2)) (.leaf (5))) (.branch 50 (.leaf (3)) (.branch 51 (.leaf (0)) (.leaf (1))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (6)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (7)) (.branch 60 (.leaf (1)) (.leaf (0)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (3)) (.leaf (5))) (.branch 64 (.leaf (1)) (.leaf (0)))) (.branch 67 (.branch 66 (.leaf (2)) (.leaf (4))) (.branch 68 (.leaf (0)) (.branch 69 (.leaf (1)) (.leaf (6)))))))))
  code := certificateD8_1077
  counts := ![(.branch 33 (.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))) (.branch 51 (.branch 40 (.branch 36 (.leaf (10)) (.leaf (11))) (.branch 44 (.leaf (12)) (.branch 47 (.leaf (13)) (.leaf (14))))) (.branch 61 (.branch 54 (.leaf (15)) (.branch 58 (.leaf (16)) (.leaf (17)))) (.branch 65 (.leaf (18)) (.branch 68 (.leaf (19)) (.leaf (20))))))),
  (.branch 34 (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 52 (.branch 43 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 60 (.branch 55 (.leaf (12)) (.leaf (13))) (.branch 64 (.leaf (14)) (.branch 69 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 67 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 42 (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 56 (.leaf (3)) (.branch 70 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 29 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 20 (.leaf (-4)) (.leaf (-5)))) (.branch 46 (.branch 37 (.leaf (-6)) (.leaf (-8))) (.branch 55 (.leaf (-9)) (.branch 64 (.leaf (-10)) (.leaf (-11)))))),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 3 (.leaf (0)) (.leaf (-26))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (-3))) (.branch 53 (.leaf (-8)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-23)))]
  high := ![(.branch 37 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-11)),
  (.branch 58 (.branch 40 (.leaf (-19)) (.branch 49 (.leaf (-18)) (.leaf (-17)))) (.branch 68 (.branch 67 (.leaf (-16)) (.leaf (-12))) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 65 (.branch 51 (.branch 39 (.leaf (-26)) (.leaf (-25))) (.branch 63 (.leaf (-24)) (.branch 64 (.leaf (-21)) (.leaf (-18))))) (.branch 67 (.branch 66 (.leaf (-15)) (.leaf (-12))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 68 (.branch 54 (.leaf (-12)) (.leaf (-11))) (.branch 69 (.leaf (-10)) (.leaf (-9)))),
  (.branch 66 (.branch 64 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-5)))) (.branch 68 (.branch 67 (.leaf (-4)) (.leaf (-3))) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 64 (.branch 61 (.branch 42 (.leaf (-23)) (.branch 60 (.leaf (-22)) (.leaf (-20)))) (.branch 62 (.leaf (-18)) (.branch 63 (.leaf (-16)) (.leaf (-14))))) (.branch 67 (.branch 65 (.leaf (-12)) (.branch 66 (.leaf (-10)) (.leaf (-8)))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2))))))]
def witnessD8_134_1078 : CycleWitness 8 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (7))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (4))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (3)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (6))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (4)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (5)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (7)) (.branch 34 (.leaf (3)) (.leaf (4)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (3)) (.leaf (0))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (4)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (7)) (.leaf (3))) (.branch 50 (.leaf (5)) (.branch 51 (.leaf (0)) (.leaf (1))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (6)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (0)) (.branch 60 (.leaf (5)) (.leaf (2)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (4)) (.leaf (0))) (.branch 64 (.leaf (7)) (.leaf (1)))) (.branch 67 (.branch 66 (.leaf (3)) (.leaf (0))) (.branch 68 (.leaf (2)) (.branch 69 (.leaf (4)) (.leaf (5)))))))))
  code := certificateD8_1078
  counts := ![(.branch 32 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 51 (.branch 39 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.branch 47 (.leaf (12)) (.leaf (13))))) (.branch 59 (.branch 55 (.leaf (14)) (.leaf (15))) (.branch 63 (.leaf (16)) (.branch 67 (.leaf (17)) (.leaf (18))))))),
  (.branch 31 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 52 (.branch 38 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 58 (.leaf (9)) (.branch 65 (.leaf (10)) (.leaf (11)))))),
  (.branch 37 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 46 (.leaf (5)) (.leaf (6))) (.branch 61 (.leaf (7)) (.branch 68 (.leaf (8)) (.leaf (9)))))),
  (.branch 34 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 66 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.branch 69 (.leaf (7)) (.leaf (8)))))),
  (.branch 40 (.branch 21 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 60 (.branch 50 (.leaf (4)) (.leaf (5))) (.branch 70 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-29))) (.branch 39 (.leaf (-36)) (.leaf (-39)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-14)) (.leaf (-19)))) (.branch 25 (.branch 19 (.leaf (-21)) (.leaf (-23))) (.branch 31 (.leaf (-25)) (.leaf (-27))))),
  (.branch 37 (.branch 6 (.leaf (0)) (.leaf (-2))) (.branch 68 (.leaf (-3)) (.leaf (-4)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 49 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.branch 69 (.leaf (-6)) (.leaf (-13)))),
  (.branch 29 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.branch 56 (.leaf (-14)) (.leaf (-16)))),
  (.branch 48 (.branch 14 (.leaf (0)) (.leaf (-5))) (.branch 64 (.leaf (-9)) (.leaf (-12))))]
  high := ![(.branch 56 (.branch 44 (.branch 40 (.leaf (-39)) (.leaf (-38))) (.branch 48 (.leaf (-37)) (.branch 52 (.leaf (-36)) (.leaf (-35))))) (.branch 64 (.branch 60 (.leaf (-34)) (.leaf (-33))) (.branch 68 (.leaf (-32)) (.branch 69 (.leaf (-22)) (.leaf (-12)))))),
  (.branch 66 (.branch 32 (.leaf (-27)) (.branch 59 (.leaf (-26)) (.leaf (-25)))) (.branch 68 (.branch 67 (.leaf (-22)) (.leaf (-19))) (.branch 69 (.leaf (-16)) (.leaf (-13))))),
  (.branch 69 (.leaf (-4)) (.leaf (-3))),
  (.branch 67 (.branch 58 (.leaf (-7)) (.leaf (-6))) (.branch 68 (.leaf (-5)) (.branch 69 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-13)),
  (.branch 61 (.branch 30 (.leaf (-8)) (.leaf (-6))) (.branch 62 (.leaf (-1)) (.leaf (0)))),
  (.branch 63 (.branch 59 (.branch 57 (.leaf (-16)) (.branch 58 (.leaf (-15)) (.leaf (-14)))) (.branch 61 (.branch 60 (.leaf (-13)) (.leaf (-12))) (.branch 62 (.leaf (-11)) (.leaf (-10))))) (.branch 66 (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7)))) (.branch 68 (.branch 67 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 67 (.branch 65 (.leaf (-12)) (.branch 66 (.leaf (-11)) (.leaf (-10)))) (.branch 68 (.leaf (-9)) (.branch 69 (.leaf (-8)) (.leaf (-7)))))]
def witnessD8_134_1079 : CycleWitness 8 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (6))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (7))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (6)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (5)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (7)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (4)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (6)) (.leaf (1))) (.branch 42 (.leaf (0)) (.leaf (5))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (3)) (.leaf (0))) (.branch 46 (.leaf (2)) (.leaf (4)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (6))) (.branch 50 (.leaf (1)) (.branch 51 (.leaf (0)) (.leaf (7))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (5)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (4))) (.branch 59 (.leaf (1)) (.branch 60 (.leaf (0)) (.leaf (6)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (0)) (.leaf (3))) (.branch 64 (.leaf (2)) (.leaf (0)))) (.branch 67 (.branch 66 (.leaf (5)) (.leaf (1))) (.branch 68 (.leaf (0)) (.branch 69 (.leaf (4)) (.leaf (7)))))))))
  code := certificateD8_1079
  counts := ![(.branch 33 (.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 27 (.leaf (9)) (.branch 30 (.leaf (10)) (.leaf (11)))))) (.branch 51 (.branch 42 (.branch 36 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14)))) (.branch 45 (.leaf (15)) (.branch 48 (.leaf (16)) (.leaf (17))))) (.branch 60 (.branch 54 (.leaf (18)) (.branch 57 (.leaf (19)) (.leaf (20)))) (.branch 65 (.branch 62 (.leaf (21)) (.leaf (22))) (.branch 68 (.leaf (23)) (.leaf (24))))))),
  (.branch 32 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 67 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.leaf (7))))),
  (.branch 38 (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 58 (.branch 47 (.leaf (4)) (.leaf (5))) (.branch 69 (.leaf (6)) (.leaf (7))))),
  (.branch 31 (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.branch 70 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 27 (.leaf (-23)) (.leaf (-26)))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-27))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-15))) (.branch 53 (.leaf (-18)) (.branch 63 (.leaf (-20)) (.leaf (-21))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-3)) (.leaf (-6)))) (.branch 38 (.leaf (-7)) (.branch 47 (.leaf (-8)) (.leaf (-11))))),
  (.branch 31 (.branch 8 (.leaf (0)) (.leaf (-4))) (.branch 66 (.leaf (-5)) (.leaf (-6)))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-8)) (.leaf (-12)))) (.branch 49 (.leaf (-13)) (.branch 61 (.leaf (-16)) (.leaf (-17))))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 66 (.branch 63 (.leaf (-26)) (.leaf (-25))) (.branch 69 (.leaf (-24)) (.leaf (-12)))),
  (.branch 68 (.leaf (-12)) (.branch 69 (.leaf (-8)) (.leaf (-4)))),
  (.branch 65 (.branch 47 (.branch 38 (.leaf (-27)) (.leaf (-26))) (.branch 56 (.leaf (-25)) (.leaf (-24)))) (.branch 67 (.branch 66 (.leaf (-20)) (.leaf (-16))) (.branch 68 (.leaf (-12)) (.branch 69 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 66 (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-19)) (.leaf (-17)))) (.branch 68 (.branch 67 (.leaf (-15)) (.leaf (-13))) (.branch 69 (.leaf (-11)) (.leaf (-9))))),
  (.branch 48 (.leaf (-11)) (.branch 59 (.leaf (-10)) (.leaf (-9)))),
  (.branch 68 (.branch 67 (.leaf (-6)) (.leaf (-5))) (.branch 69 (.leaf (-4)) (.leaf (-3)))),
  (.branch 65 (.branch 63 (.branch 62 (.leaf (-17)) (.leaf (-16))) (.branch 64 (.leaf (-15)) (.leaf (-14)))) (.branch 67 (.branch 66 (.leaf (-13)) (.leaf (-12))) (.branch 68 (.leaf (-11)) (.branch 69 (.leaf (-10)) (.leaf (-9)))))),
  (.branch 53 (.leaf (-1)) (.leaf (0)))]
def witnessD8_134_1080 : CycleWitness 8 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (2))) (.branch 11 (.leaf (6)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (5)) (.leaf (2))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (4)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (2))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (7)) (.leaf (5)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (3)) (.leaf (1))) (.branch 29 (.leaf (4)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (6))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (1)) (.leaf (5)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (4)) (.leaf (1)))) (.branch 41 (.branch 40 (.leaf (6)) (.leaf (3))) (.branch 42 (.leaf (0)) (.leaf (7))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (1)) (.leaf (2))) (.branch 46 (.leaf (5)) (.leaf (4)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (3))) (.branch 50 (.leaf (1)) (.branch 51 (.leaf (6)) (.leaf (2))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (3))) (.branch 55 (.leaf (4)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (5)) (.leaf (2))) (.branch 59 (.leaf (0)) (.branch 60 (.leaf (7)) (.leaf (6)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (3)) (.leaf (1))) (.branch 64 (.leaf (4)) (.leaf (0)))) (.branch 67 (.branch 66 (.leaf (2)) (.leaf (5))) (.branch 68 (.leaf (3)) (.branch 69 (.leaf (1)) (.leaf (6)))))))))
  code := certificateD8_1080
  counts := ![(.branch 30 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 39 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 63 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 69 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 37 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 66 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 41 (.leaf (5)) (.branch 49 (.leaf (6)) (.leaf (7)))) (.branch 62 (.leaf (8)) (.branch 68 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 57 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 67 (.leaf (6)) (.leaf (7))))),
  (.branch 40 (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))) (.branch 61 (.branch 51 (.leaf (4)) (.leaf (5))) (.branch 70 (.leaf (6)) (.leaf (7))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-29)) (.leaf (-32)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 44 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 33 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-3)) (.leaf (-7)))) (.branch 54 (.leaf (-9)) (.branch 68 (.leaf (-12)) (.leaf (-14))))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-23)) (.leaf (-25)))),
  (.branch 5 (.leaf (0)) (.branch 35 (.leaf (-11)) (.leaf (-14)))),
  (.branch 40 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-19)) (.leaf (-20))))]
  high := ![(.branch 66 (.branch 54 (.leaf (-32)) (.branch 60 (.leaf (-31)) (.leaf (-30)))) (.branch 68 (.branch 67 (.leaf (-24)) (.leaf (-18))) (.branch 69 (.leaf (-12)) (.leaf (-6))))),
  (.branch 57 (.leaf (-4)) (.leaf (-3))),
  (.branch 67 (.branch 59 (.leaf (-5)) (.leaf (-4))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.branch 69 (.leaf (-14)) (.leaf (-12))),
  (.branch 66 (.branch 56 (.leaf (-25)) (.branch 65 (.leaf (-24)) (.leaf (-20)))) (.branch 68 (.branch 67 (.leaf (-16)) (.leaf (-12))) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.branch 68 (.branch 36 (.leaf (-14)) (.leaf (-13))) (.branch 69 (.leaf (-11)) (.leaf (-9)))),
  (.branch 62 (.leaf (-4)) (.branch 63 (.leaf (-2)) (.leaf (0)))),
  (.branch 65 (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-18))) (.branch 63 (.leaf (-16)) (.branch 64 (.leaf (-14)) (.leaf (-12))))) (.branch 67 (.branch 66 (.leaf (-10)) (.leaf (-8))) (.branch 68 (.leaf (-6)) (.branch 69 (.leaf (-4)) (.leaf (-2))))))]
def witnessD8_134_1081 : CycleWitness 8 where
  length := 70
  word := (.branch 35 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (2)) (.leaf (5))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (6)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (7)) (.branch 25 (.leaf (0)) (.leaf (5)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (3))) (.branch 29 (.leaf (4)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (6))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (5)) (.leaf (3)))))))) (.branch 52 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (4)) (.leaf (1)))) (.branch 41 (.branch 40 (.leaf (7)) (.leaf (3))) (.branch 42 (.leaf (0)) (.leaf (5))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (2)) (.leaf (1))) (.branch 46 (.leaf (4)) (.leaf (6)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (3))) (.branch 50 (.leaf (1)) (.branch 51 (.leaf (2)) (.leaf (5))))))) (.branch 61 (.branch 56 (.branch 54 (.branch 53 (.leaf (7)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (2))) (.branch 59 (.leaf (6)) (.branch 60 (.leaf (0)) (.leaf (5)))))) (.branch 65 (.branch 63 (.branch 62 (.leaf (1)) (.leaf (3))) (.branch 64 (.leaf (4)) (.leaf (2)))) (.branch 67 (.branch 66 (.leaf (0)) (.leaf (7))) (.branch 68 (.leaf (1)) (.branch 69 (.leaf (5)) (.leaf (3)))))))))
  code := certificateD8_1081
  counts := ![(.branch 31 (.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 50 (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 62 (.branch 57 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 65 (.leaf (9)) (.leaf (10)))))),
  (.branch 35 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 56 (.branch 41 (.leaf (5)) (.branch 49 (.leaf (6)) (.leaf (7)))) (.branch 63 (.leaf (8)) (.branch 70 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.branch 69 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 40 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 53 (.leaf (3)) (.branch 67 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-29))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 50 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-23)) (.leaf (-26)))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (-3)) (.leaf (-4)))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (-10))) (.branch 32 (.leaf (-12)) (.branch 59 (.leaf (-13)) (.leaf (-16))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (-3))) (.branch 53 (.leaf (-6)) (.branch 67 (.leaf (-7)) (.leaf (-8)))))]
  high := ![(.branch 55 (.branch 43 (.branch 37 (.leaf (-29)) (.leaf (-28))) (.branch 49 (.leaf (-27)) (.leaf (-26)))) (.branch 67 (.branch 61 (.leaf (-25)) (.leaf (-24))) (.branch 68 (.leaf (-18)) (.branch 69 (.leaf (-12)) (.leaf (-6)))))),
  (.branch 69 (.leaf (-4)) (.leaf (-3))),
  (.branch 67 (.branch 66 (.leaf (-5)) (.leaf (-4))) (.branch 68 (.leaf (-3)) (.branch 69 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 66 (.branch 56 (.branch 47 (.leaf (-26)) (.leaf (-25))) (.branch 65 (.leaf (-24)) (.leaf (-20)))) (.branch 68 (.branch 67 (.leaf (-16)) (.leaf (-12))) (.branch 69 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-4)),
  (.branch 64 (.branch 61 (.branch 60 (.leaf (-16)) (.leaf (-15))) (.branch 62 (.leaf (-14)) (.branch 63 (.leaf (-13)) (.leaf (-12))))) (.branch 67 (.branch 65 (.leaf (-11)) (.branch 66 (.leaf (-10)) (.leaf (-9)))) (.branch 68 (.leaf (-8)) (.branch 69 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 68 (.leaf (-8)) (.branch 69 (.leaf (-7)) (.leaf (-6))))]
def witnessD8_134_1082 : CycleWitness 8 where
  length := 69
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (3)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (5)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (1)) (.leaf (0)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (2)) (.leaf (1))) (.branch 37 (.leaf (0)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (3)) (.leaf (2))) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (6)) (.leaf (0))) (.branch 45 (.leaf (2)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 50 (.leaf (0)) (.leaf (3))))))) (.branch 60 (.branch 55 (.branch 53 (.branch 52 (.leaf (1)) (.leaf (2))) (.branch 54 (.leaf (0)) (.leaf (4)))) (.branch 57 (.branch 56 (.leaf (1)) (.leaf (0))) (.branch 58 (.leaf (2)) (.branch 59 (.leaf (1)) (.leaf (0)))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (1)) (.leaf (3))) (.branch 63 (.leaf (2)) (.leaf (0)))) (.branch 66 (.branch 65 (.leaf (1)) (.leaf (7))) (.branch 67 (.leaf (0)) (.branch 68 (.leaf (2)) (.leaf (1)))))))))
  code := certificateD8_1082
  counts := ![(.branch 34 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))) (.branch 50 (.branch 41 (.branch 37 (.leaf (11)) (.leaf (12))) (.branch 44 (.leaf (13)) (.branch 47 (.leaf (14)) (.leaf (15))))) (.branch 60 (.branch 54 (.leaf (16)) (.branch 57 (.leaf (17)) (.leaf (18)))) (.branch 64 (.leaf (19)) (.branch 67 (.leaf (20)) (.leaf (21))))))),
  (.branch 36 (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))) (.branch 52 (.branch 42 (.branch 38 (.leaf (11)) (.leaf (12))) (.branch 46 (.leaf (13)) (.branch 48 (.leaf (14)) (.leaf (15))))) (.branch 61 (.branch 56 (.leaf (16)) (.branch 59 (.leaf (17)) (.leaf (18)))) (.branch 65 (.leaf (19)) (.branch 69 (.leaf (20)) (.leaf (21))))))),
  (.branch 35 (.branch 17 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))) (.branch 53 (.branch 45 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 49 (.leaf (10)) (.leaf (11)))) (.branch 63 (.branch 58 (.leaf (12)) (.leaf (13))) (.branch 68 (.leaf (14)) (.leaf (15)))))),
  (.branch 28 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1))),
  (.branch 66 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-16)) (.leaf (-18)))),
  (.branch 25 (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-5)))) (.branch 48 (.branch 38 (.leaf (-6)) (.leaf (-8))) (.branch 61 (.leaf (-9)) (.leaf (-11))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 30 (.leaf (-7)) (.branch 53 (.leaf (-8)) (.leaf (-9))))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-13)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-14))),
  (.branch 20 (.leaf (0)) (.leaf (-49))),
  (.branch 43 (.leaf (0)) (.leaf (-26))),
  (.branch 66 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 61 (.branch 51 (.leaf (-18)) (.leaf (-17))) (.branch 68 (.leaf (-14)) (.leaf (-7)))),
  (.branch 66 (.branch 62 (.leaf (-11)) (.leaf (-10))) (.branch 67 (.leaf (-8)) (.branch 68 (.leaf (-6)) (.leaf (-4))))),
  (.branch 59 (.branch 54 (.leaf (-9)) (.leaf (-8))) (.branch 64 (.leaf (-7)) (.leaf (-6)))),
  (.branch 65 (.branch 63 (.leaf (-14)) (.branch 64 (.leaf (-12)) (.leaf (-10)))) (.branch 67 (.branch 66 (.leaf (-8)) (.leaf (-6))) (.branch 68 (.leaf (-4)) (.leaf (-2))))),
  (.branch 62 (.branch 58 (.branch 56 (.leaf (-14)) (.branch 57 (.leaf (-13)) (.leaf (-12)))) (.branch 60 (.branch 59 (.leaf (-11)) (.leaf (-10))) (.branch 61 (.leaf (-9)) (.leaf (-8))))) (.branch 65 (.branch 63 (.leaf (-7)) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 67 (.branch 66 (.leaf (-4)) (.leaf (-3))) (.branch 68 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 44 (.branch 32 (.branch 26 (.branch 23 (.branch 21 (.leaf (-49)) (.branch 22 (.leaf (-48)) (.leaf (-47)))) (.branch 24 (.leaf (-46)) (.branch 25 (.leaf (-45)) (.leaf (-44))))) (.branch 29 (.branch 27 (.leaf (-43)) (.branch 28 (.leaf (-42)) (.leaf (-41)))) (.branch 30 (.leaf (-40)) (.branch 31 (.leaf (-39)) (.leaf (-38)))))) (.branch 38 (.branch 35 (.branch 33 (.leaf (-37)) (.branch 34 (.leaf (-36)) (.leaf (-35)))) (.branch 36 (.leaf (-34)) (.branch 37 (.leaf (-33)) (.leaf (-32))))) (.branch 41 (.branch 39 (.leaf (-31)) (.branch 40 (.leaf (-30)) (.leaf (-29)))) (.branch 42 (.leaf (-28)) (.branch 43 (.leaf (-27)) (.leaf (-26))))))) (.branch 56 (.branch 50 (.branch 47 (.branch 45 (.leaf (-25)) (.branch 46 (.leaf (-24)) (.leaf (-23)))) (.branch 48 (.leaf (-22)) (.branch 49 (.leaf (-21)) (.leaf (-20))))) (.branch 53 (.branch 51 (.leaf (-19)) (.branch 52 (.leaf (-18)) (.leaf (-17)))) (.branch 54 (.leaf (-16)) (.branch 55 (.leaf (-15)) (.leaf (-14)))))) (.branch 62 (.branch 59 (.branch 57 (.leaf (-13)) (.branch 58 (.leaf (-12)) (.leaf (-11)))) (.branch 60 (.leaf (-10)) (.branch 61 (.leaf (-9)) (.leaf (-8))))) (.branch 65 (.branch 63 (.leaf (-7)) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 67 (.branch 66 (.leaf (-4)) (.leaf (-3))) (.branch 68 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 56 (.branch 49 (.branch 46 (.branch 44 (.leaf (-26)) (.branch 45 (.leaf (-25)) (.leaf (-24)))) (.branch 47 (.leaf (-23)) (.branch 48 (.leaf (-22)) (.leaf (-21))))) (.branch 52 (.branch 50 (.leaf (-20)) (.branch 51 (.leaf (-19)) (.leaf (-18)))) (.branch 54 (.branch 53 (.leaf (-17)) (.leaf (-16))) (.branch 55 (.leaf (-15)) (.leaf (-14)))))) (.branch 62 (.branch 59 (.branch 57 (.leaf (-13)) (.branch 58 (.leaf (-12)) (.leaf (-11)))) (.branch 60 (.leaf (-10)) (.branch 61 (.leaf (-9)) (.leaf (-8))))) (.branch 65 (.branch 63 (.leaf (-7)) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 67 (.branch 66 (.leaf (-4)) (.leaf (-3))) (.branch 68 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 67 (.leaf (-3)) (.branch 68 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_134_1083 : CycleWitness 8 where
  length := 69
  word := (.branch 34 (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (7))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (5))) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (6))) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (4)) (.leaf (1))) (.branch 28 (.leaf (7)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (1))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (2)) (.leaf (0)))))))) (.branch 51 (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (3)) (.leaf (1))) (.branch 37 (.leaf (6)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (4)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (7))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (0)) (.leaf (3))) (.branch 45 (.leaf (1)) (.leaf (5)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (2))) (.branch 49 (.leaf (4)) (.branch 50 (.leaf (1)) (.leaf (6))))))) (.branch 60 (.branch 55 (.branch 53 (.branch 52 (.leaf (0)) (.leaf (3))) (.branch 54 (.leaf (1)) (.leaf (7)))) (.branch 57 (.branch 56 (.leaf (2)) (.leaf (0))) (.branch 58 (.leaf (3)) (.branch 59 (.leaf (1)) (.leaf (5)))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (0)) (.leaf (4))) (.branch 63 (.leaf (1)) (.leaf (2)))) (.branch 66 (.branch 65 (.leaf (6)) (.leaf (0))) (.branch 67 (.leaf (3)) (.branch 68 (.leaf (1)) (.leaf (7)))))))))
  code := certificateD8_1083
  counts := ![(.branch 34 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 52 (.branch 43 (.branch 38 (.leaf (8)) (.leaf (9))) (.branch 47 (.leaf (10)) (.leaf (11)))) (.branch 61 (.branch 57 (.leaf (12)) (.leaf (13))) (.branch 66 (.leaf (14)) (.leaf (15)))))),
  (.branch 36 (.branch 17 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))) (.branch 54 (.branch 45 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 50 (.leaf (10)) (.leaf (11)))) (.branch 63 (.branch 59 (.leaf (12)) (.leaf (13))) (.branch 68 (.leaf (14)) (.leaf (15)))))),
  (.branch 33 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 41 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))) (.branch 53 (.branch 44 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 67 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 65 (.leaf (4)) (.leaf (5))))),
  (.branch 42 (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 55 (.leaf (3)) (.branch 69 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-18))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 17 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-17))),
  (.branch 12 (.branch 7 (.leaf (0)) (.leaf (-3))) (.branch 35 (.leaf (-10)) (.branch 58 (.leaf (-15)) (.leaf (-20))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 49 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.branch 32 (.leaf (-44)) (.leaf (-47)))),
  (.branch 9 (.leaf (0)) (.leaf (-24))),
  (.branch 55 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 62 (.branch 48 (.leaf (-18)) (.leaf (-17))) (.branch 67 (.leaf (-15)) (.branch 68 (.leaf (-10)) (.leaf (-5))))),
  (.branch 64 (.leaf (-7)) (.leaf (-5))),
  (.branch 65 (.branch 49 (.leaf (-17)) (.branch 57 (.leaf (-16)) (.leaf (-15)))) (.branch 67 (.branch 66 (.leaf (-12)) (.leaf (-9))) (.branch 68 (.leaf (-6)) (.leaf (-3))))),
  (.branch 59 (.leaf (-20)) (.branch 68 (.leaf (-19)) (.leaf (-17)))),
  (.branch 65 (.branch 63 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 64 (.leaf (-9)) (.leaf (-8)))) (.branch 67 (.branch 66 (.leaf (-7)) (.leaf (-6))) (.branch 68 (.leaf (-5)) (.leaf (-4))))),
  (.branch 63 (.branch 47 (.branch 33 (.leaf (-47)) (.leaf (-46))) (.branch 61 (.leaf (-45)) (.branch 62 (.leaf (-40)) (.leaf (-35))))) (.branch 66 (.branch 64 (.leaf (-30)) (.branch 65 (.leaf (-25)) (.leaf (-20)))) (.branch 67 (.leaf (-15)) (.branch 68 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 52 (.branch 24 (.branch 10 (.leaf (-24)) (.leaf (-23))) (.branch 38 (.leaf (-22)) (.leaf (-21)))) (.branch 67 (.branch 66 (.leaf (-20)) (.leaf (-15))) (.branch 68 (.leaf (-10)) (.leaf (-5))))),
  (.branch 56 (.leaf (-1)) (.leaf (0)))]
def witnessD8_134_1084 : CycleWitness 8 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (1)) (.leaf (0))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (5)) (.leaf (0))) (.branch 33 (.leaf (1)) (.leaf (2))))))) (.branch 51 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (3))) (.branch 42 (.leaf (1)) (.leaf (0))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (2)) (.leaf (0))) (.branch 46 (.leaf (1)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (4)) (.leaf (0))) (.branch 50 (.leaf (1)) (.leaf (2)))))) (.branch 60 (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (7))) (.branch 59 (.leaf (1)) (.leaf (0))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (2)) (.leaf (0))) (.branch 63 (.leaf (1)) (.leaf (0)))) (.branch 66 (.branch 65 (.leaf (5)) (.leaf (0))) (.branch 67 (.leaf (1)) (.leaf (2))))))))
  code := certificateD8_1084
  counts := ![(.branch 32 (.branch 15 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 23 (.branch 19 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 21 (.leaf (10)) (.leaf (11)))) (.branch 28 (.branch 26 (.leaf (12)) (.leaf (13))) (.branch 30 (.leaf (14)) (.leaf (15)))))) (.branch 49 (.branch 40 (.branch 36 (.branch 35 (.leaf (16)) (.leaf (17))) (.branch 38 (.leaf (18)) (.leaf (19)))) (.branch 45 (.branch 43 (.leaf (20)) (.leaf (21))) (.branch 47 (.leaf (22)) (.leaf (23))))) (.branch 57 (.branch 53 (.branch 52 (.leaf (24)) (.leaf (25))) (.branch 55 (.leaf (26)) (.leaf (27)))) (.branch 62 (.branch 60 (.leaf (28)) (.leaf (29))) (.branch 64 (.leaf (30)) (.branch 66 (.leaf (31)) (.leaf (32)))))))),
  (.branch 33 (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 50 (.branch 42 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 59 (.branch 54 (.leaf (12)) (.leaf (13))) (.branch 63 (.leaf (14)) (.branch 67 (.leaf (15)) (.leaf (16))))))),
  (.branch 34 (.branch 17 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 39 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 61 (.branch 56 (.leaf (9)) (.leaf (10))) (.branch 68 (.leaf (11)) (.leaf (12)))))),
  (.branch 7 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 31 (.leaf (0)) (.branch 65 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 58 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 23 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))) (.branch 19 (.branch 6 (.leaf (-13)) (.leaf (-14))) (.branch 21 (.leaf (-15)) (.leaf (-16))))) (.branch 40 (.branch 36 (.leaf (-17)) (.branch 38 (.leaf (-18)) (.leaf (-19)))) (.branch 55 (.branch 53 (.leaf (-20)) (.leaf (-21))) (.branch 57 (.leaf (-22)) (.leaf (-23)))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))) (.branch 44 (.leaf (-3)) (.branch 61 (.leaf (-4)) (.leaf (-5))))),
  (.branch 7 (.leaf (0)) (.leaf (-27))),
  (.branch 14 (.leaf (0)) (.leaf (-20))),
  (.branch 31 (.leaf (0)) (.leaf (-3))),
  (.branch 24 (.leaf (0)) (.leaf (-44))),
  (.branch 58 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 58 (.leaf (-23)) (.branch 67 (.leaf (-22)) (.leaf (-17)))),
  (.branch 55 (.leaf (-5)) (.leaf (-4))),
  (.branch 64 (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3)))) (.branch 65 (.leaf (-2)) (.branch 66 (.leaf (-1)) (.leaf (0))))),
  (.branch 54 (.branch 47 (.branch 44 (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-26)) (.leaf (-25)))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-23)) (.leaf (-22))))) (.branch 50 (.branch 48 (.leaf (-21)) (.branch 49 (.leaf (-20)) (.leaf (-19)))) (.branch 52 (.branch 51 (.leaf (-18)) (.leaf (-17))) (.branch 53 (.leaf (-16)) (.leaf (-15)))))) (.branch 61 (.branch 57 (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))) (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.leaf (-8))))) (.branch 64 (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.branch 53 (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-19))) (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-17)) (.leaf (-16))))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-14))) (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))))) (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 35 (.branch 29 (.branch 26 (.branch 25 (.leaf (-44)) (.leaf (-43))) (.branch 27 (.leaf (-42)) (.branch 28 (.leaf (-41)) (.leaf (-40))))) (.branch 32 (.branch 30 (.leaf (-39)) (.branch 31 (.leaf (-38)) (.leaf (-37)))) (.branch 33 (.leaf (-36)) (.branch 34 (.leaf (-35)) (.leaf (-34)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-33)) (.leaf (-32))) (.branch 38 (.leaf (-31)) (.branch 39 (.leaf (-30)) (.leaf (-29))))) (.branch 43 (.branch 41 (.leaf (-28)) (.branch 42 (.leaf (-27)) (.leaf (-26)))) (.branch 44 (.leaf (-25)) (.branch 45 (.leaf (-24)) (.leaf (-23))))))) (.branch 57 (.branch 51 (.branch 48 (.branch 47 (.leaf (-22)) (.leaf (-21))) (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-19)) (.leaf (-18))))) (.branch 54 (.branch 52 (.leaf (-17)) (.branch 53 (.leaf (-16)) (.leaf (-15)))) (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))))) (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_134_1085 : CycleWitness 8 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (7))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (5)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (0)) (.leaf (3)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.leaf (7))))))) (.branch 51 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (5))) (.branch 42 (.leaf (0)) (.leaf (1))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (6))) (.branch 46 (.leaf (0)) (.leaf (3)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (0)) (.leaf (4)))))) (.branch 60 (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (7))) (.branch 59 (.leaf (0)) (.leaf (1))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (0)) (.leaf (5))) (.branch 63 (.leaf (0)) (.leaf (3)))) (.branch 66 (.branch 65 (.leaf (0)) (.leaf (1))) (.branch 67 (.leaf (0)) (.leaf (6))))))))
  code := certificateD8_1085
  counts := ![(.branch 33 (.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 23 (.branch 19 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.leaf (12)))) (.branch 27 (.branch 25 (.leaf (13)) (.leaf (14))) (.branch 29 (.leaf (15)) (.branch 31 (.leaf (16)) (.leaf (17))))))) (.branch 50 (.branch 40 (.branch 36 (.branch 35 (.leaf (18)) (.leaf (19))) (.branch 38 (.leaf (20)) (.leaf (21)))) (.branch 44 (.branch 42 (.leaf (22)) (.leaf (23))) (.branch 46 (.leaf (24)) (.branch 48 (.leaf (25)) (.leaf (26)))))) (.branch 59 (.branch 53 (.branch 52 (.leaf (27)) (.leaf (28))) (.branch 55 (.leaf (29)) (.branch 57 (.leaf (30)) (.leaf (31))))) (.branch 63 (.branch 61 (.leaf (32)) (.leaf (33))) (.branch 65 (.leaf (34)) (.branch 67 (.leaf (35)) (.leaf (36)))))))),
  (.branch 32 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3)))),
  (.branch 45 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 68 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.branch 28 (.leaf (-16)) (.leaf (-18)))),
  (.branch 17 (.leaf (0)) (.branch 62 (.leaf (-6)) (.leaf (-7)))),
  (.branch 45 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 60 (.branch 56 (.branch 54 (.leaf (-16)) (.leaf (-15))) (.branch 58 (.leaf (-14)) (.leaf (-13)))) (.branch 64 (.branch 62 (.leaf (-12)) (.leaf (-11))) (.branch 66 (.leaf (-10)) (.leaf (-9))))),
  (.branch 61 (.branch 55 (.leaf (-8)) (.leaf (-7))) (.branch 67 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-11)) (.leaf (-10)))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1)))),
  (.branch 59 (.branch 55 (.branch 53 (.branch 52 (.leaf (-18)) (.leaf (-17))) (.branch 54 (.leaf (-16)) (.leaf (-15)))) (.branch 57 (.branch 56 (.leaf (-14)) (.leaf (-13))) (.branch 58 (.leaf (-12)) (.leaf (-11))))) (.branch 63 (.branch 61 (.branch 60 (.leaf (-10)) (.leaf (-9))) (.branch 62 (.leaf (-8)) (.leaf (-7)))) (.branch 65 (.branch 64 (.leaf (-6)) (.leaf (-5))) (.branch 66 (.leaf (-4)) (.branch 67 (.leaf (-3)) (.leaf (-2))))))),
  (.branch 65 (.branch 63 (.leaf (-7)) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.leaf (-4)) (.branch 67 (.leaf (-3)) (.leaf (-2))))),
  (.branch 46 (.leaf (-1)) (.leaf (0))),
  (.branch 62 (.branch 59 (.branch 35 (.leaf (-12)) (.leaf (-11))) (.branch 60 (.leaf (-10)) (.branch 61 (.leaf (-9)) (.leaf (-8))))) (.branch 65 (.branch 63 (.leaf (-7)) (.branch 64 (.leaf (-6)) (.leaf (-5)))) (.branch 66 (.leaf (-4)) (.branch 67 (.leaf (-3)) (.leaf (-2))))))]
def witnessD8_134_1086 : CycleWitness 8 where
  length := 68
  word := (.branch 34 (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (4)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (6)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.leaf (3))))))) (.branch 51 (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (4)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (2))) (.branch 42 (.leaf (0)) (.leaf (1))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (3))) (.branch 46 (.leaf (0)) (.leaf (5)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (0)) (.leaf (2)))))) (.branch 60 (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (4)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (0)) (.leaf (1))))) (.branch 64 (.branch 62 (.branch 61 (.leaf (0)) (.leaf (2))) (.branch 63 (.leaf (0)) (.leaf (7)))) (.branch 66 (.branch 65 (.leaf (0)) (.leaf (1))) (.branch 67 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_1086
  counts := ![(.branch 33 (.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 23 (.branch 19 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.leaf (12)))) (.branch 27 (.branch 25 (.leaf (13)) (.leaf (14))) (.branch 29 (.leaf (15)) (.branch 31 (.leaf (16)) (.leaf (17))))))) (.branch 50 (.branch 40 (.branch 36 (.branch 35 (.leaf (18)) (.leaf (19))) (.branch 38 (.leaf (20)) (.leaf (21)))) (.branch 44 (.branch 42 (.leaf (22)) (.leaf (23))) (.branch 46 (.leaf (24)) (.branch 48 (.leaf (25)) (.leaf (26)))))) (.branch 59 (.branch 53 (.branch 52 (.leaf (27)) (.leaf (28))) (.branch 55 (.leaf (29)) (.branch 57 (.leaf (30)) (.leaf (31))))) (.branch 63 (.branch 61 (.leaf (32)) (.leaf (33))) (.branch 65 (.leaf (34)) (.branch 67 (.leaf (35)) (.leaf (36)))))))),
  (.branch 32 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 58 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 64 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-5)) (.leaf (-7)))) (.branch 51 (.leaf (-8)) (.branch 62 (.leaf (-9)) (.leaf (-10))))),
  (.branch 34 (.branch 11 (.leaf (0)) (.leaf (-1))) (.branch 45 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-21))),
  (.branch 30 (.leaf (0)) (.leaf (-38))),
  (.branch 64 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 60 (.branch 56 (.branch 54 (.leaf (-16)) (.leaf (-15))) (.branch 58 (.leaf (-14)) (.leaf (-13)))) (.branch 64 (.branch 62 (.leaf (-12)) (.leaf (-11))) (.branch 66 (.leaf (-10)) (.leaf (-9))))),
  (.branch 61 (.branch 55 (.leaf (-8)) (.leaf (-7))) (.branch 67 (.leaf (-6)) (.leaf (-3)))),
  (.branch 65 (.branch 63 (.leaf (-10)) (.branch 64 (.leaf (-9)) (.leaf (-8)))) (.branch 66 (.leaf (-7)) (.branch 67 (.leaf (-6)) (.leaf (-5))))),
  (.branch 59 (.branch 46 (.leaf (-3)) (.leaf (-2))) (.branch 60 (.leaf (-1)) (.leaf (0)))),
  (.branch 62 (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-11)) (.leaf (-10)))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 52 (.branch 49 (.branch 48 (.leaf (-21)) (.leaf (-20))) (.branch 50 (.leaf (-19)) (.branch 51 (.leaf (-18)) (.leaf (-17))))) (.branch 54 (.branch 53 (.leaf (-16)) (.leaf (-15))) (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12)))))) (.branch 62 (.branch 59 (.branch 58 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-8)) (.leaf (-7))))) (.branch 65 (.branch 63 (.leaf (-6)) (.branch 64 (.leaf (-5)) (.leaf (-4)))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 39 (.branch 34 (.branch 32 (.branch 31 (.leaf (-38)) (.leaf (-37))) (.branch 33 (.leaf (-36)) (.leaf (-35)))) (.branch 36 (.branch 35 (.leaf (-34)) (.leaf (-33))) (.branch 37 (.leaf (-32)) (.branch 38 (.leaf (-31)) (.leaf (-30)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (-29)) (.leaf (-28))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-26)) (.leaf (-25))))) (.branch 46 (.branch 45 (.leaf (-24)) (.leaf (-23))) (.branch 47 (.leaf (-22)) (.branch 48 (.leaf (-21)) (.leaf (-20))))))) (.branch 58 (.branch 53 (.branch 51 (.branch 50 (.leaf (-19)) (.leaf (-18))) (.branch 52 (.leaf (-17)) (.leaf (-16)))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-14))) (.branch 56 (.leaf (-13)) (.branch 57 (.leaf (-12)) (.leaf (-11)))))) (.branch 63 (.branch 60 (.branch 59 (.leaf (-10)) (.leaf (-9))) (.branch 61 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-6))))) (.branch 65 (.branch 64 (.leaf (-5)) (.leaf (-4))) (.branch 66 (.leaf (-3)) (.branch 67 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 66 (.branch 65 (.leaf (-4)) (.leaf (-3))) (.branch 67 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_134 : Fin 14 → CycleWitness 8 := ![witnessD8_134_1073, witnessD8_134_1074, witnessD8_134_1075, witnessD8_134_1076, witnessD8_134_1077, witnessD8_134_1078, witnessD8_134_1079, witnessD8_134_1080, witnessD8_134_1081, witnessD8_134_1082, witnessD8_134_1083, witnessD8_134_1084, witnessD8_134_1085, witnessD8_134_1086]
end RealPinwheel.FiveSixths


