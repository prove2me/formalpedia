-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_023
-- name    : RealPinwheel_FiveSixths_WitnessD7_023
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:36:38.249211+00:00
-- url     : https://prove2.me/theorems/13622374-29cd-41ad-9278-c1afc5ab388b
-- title:
--   Exact witness block D7_023
-- statement:
--   These exact witnesses represent words 242 through 257 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 242–257; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_023_241 : CycleWitness 7 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (4)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (1)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (6))) (.branch 18 (.leaf (3)) (.leaf (1)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (0)) (.leaf (3))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (1)) (.leaf (4))) (.branch 26 (.leaf (0)) (.leaf (2)))) (.branch 29 (.branch 28 (.leaf (5)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (3))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (3))) (.branch 37 (.leaf (1)) (.leaf (6))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (4)) (.leaf (1)))) (.branch 44 (.branch 43 (.leaf (0)) (.leaf (3))) (.branch 45 (.leaf (1)) (.leaf (2)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (0)) (.leaf (5))) (.branch 49 (.leaf (3)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (0)) (.leaf (3))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (1)) (.leaf (4))) (.branch 57 (.leaf (0)) (.leaf (2)))) (.branch 60 (.branch 59 (.leaf (6)) (.leaf (1))) (.branch 61 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_241
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 47 (.branch 35 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.branch 43 (.leaf (12)) (.leaf (13))))) (.branch 53 (.branch 51 (.leaf (14)) (.leaf (15))) (.branch 57 (.leaf (16)) (.branch 61 (.leaf (17)) (.leaf (18))))))),
  (.branch 29 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 55 (.branch 50 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 27 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 36 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 22 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))) (.branch 35 (.branch 32 (.leaf (-17)) (.leaf (-22))) (.branch 53 (.leaf (-25)) (.leaf (-28))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))) (.branch 37 (.leaf (-14)) (.branch 45 (.leaf (-15)) (.leaf (-19))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-16)) (.leaf (-17)))) (.branch 21 (.leaf (-18)) (.branch 27 (.leaf (-19)) (.leaf (-20))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-2)) (.leaf (-3)))) (.branch 49 (.branch 36 (.leaf (-5)) (.leaf (-6))) (.branch 54 (.leaf (-7)) (.leaf (-9))))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.branch 48 (.leaf (-41)) (.leaf (-42)))),
  (.branch 17 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 54 (.leaf (-28)) (.branch 58 (.leaf (-27)) (.leaf (-26)))),
  (.branch 51 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 56 (.leaf (-17)) (.branch 61 (.leaf (-16)) (.leaf (-13))))),
  (.branch 60 (.branch 59 (.leaf (-20)) (.leaf (-15))) (.branch 61 (.leaf (-10)) (.leaf (-5)))),
  (.branch 58 (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6)))) (.branch 60 (.branch 59 (.leaf (-5)) (.leaf (-4))) (.branch 61 (.leaf (-3)) (.leaf (-2))))),
  (.branch 59 (.branch 57 (.leaf (-12)) (.branch 58 (.leaf (-10)) (.leaf (-8)))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2))))),
  (.branch 55 (.branch 51 (.branch 49 (.leaf (-42)) (.branch 50 (.leaf (-39)) (.leaf (-36)))) (.branch 53 (.branch 52 (.leaf (-33)) (.leaf (-30))) (.branch 54 (.leaf (-27)) (.leaf (-24))))) (.branch 58 (.branch 56 (.leaf (-21)) (.branch 57 (.leaf (-18)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 39 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-6)) (.leaf (-3)))))]
def witnessD7_023_242 : CycleWitness 7 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (6)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (4))) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (6))) (.branch 22 (.leaf (0)) (.leaf (5))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (3)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (1)))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (4))) (.branch 30 (.leaf (0)) (.leaf (3))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (0))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (3)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (2)))) (.branch 44 (.branch 43 (.leaf (4)) (.leaf (0))) (.branch 45 (.leaf (1)) (.leaf (3)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (0)) (.leaf (5))) (.branch 49 (.leaf (2)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (6))) (.branch 53 (.leaf (0)) (.leaf (4))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (3)) (.leaf (0))) (.branch 57 (.leaf (2)) (.leaf (1)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (5))) (.branch 61 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_242
  counts := ![(.branch 30 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 28 (.leaf (9)) (.leaf (10)))))) (.branch 47 (.branch 38 (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13)))) (.branch 41 (.leaf (14)) (.branch 44 (.leaf (15)) (.leaf (16))))) (.branch 56 (.branch 50 (.leaf (17)) (.branch 53 (.leaf (18)) (.leaf (19)))) (.branch 59 (.leaf (20)) (.branch 61 (.leaf (21)) (.leaf (22))))))),
  (.branch 27 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 33 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 12 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 32 (.leaf (-17)) (.leaf (-24)))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-15)))) (.branch 45 (.leaf (-16)) (.branch 51 (.leaf (-17)) (.leaf (-18))))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-19)) (.leaf (-21)))),
  (.branch 15 (.leaf (0)) (.branch 46 (.leaf (-1)) (.leaf (-2)))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (-8))) (.branch 29 (.leaf (-9)) (.branch 54 (.leaf (-10)) (.leaf (-11))))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (-1))) (.branch 48 (.leaf (-3)) (.branch 60 (.leaf (-4)) (.leaf (-5))))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (-19)) (.leaf (-20))))]
  high := ![(.branch 33 (.leaf (-24)) (.leaf (-23))),
  (.branch 59 (.branch 52 (.leaf (-18)) (.leaf (-16))) (.branch 60 (.leaf (-13)) (.branch 61 (.leaf (-10)) (.leaf (-7))))),
  (.branch 59 (.branch 50 (.leaf (-21)) (.branch 58 (.leaf (-20)) (.leaf (-16)))) (.branch 60 (.leaf (-12)) (.branch 61 (.leaf (-8)) (.leaf (-4))))),
  (.branch 47 (.leaf (-2)) (.branch 56 (.leaf (-1)) (.leaf (0)))),
  (.branch 58 (.branch 56 (.branch 55 (.leaf (-11)) (.leaf (-10))) (.branch 57 (.leaf (-9)) (.leaf (-8)))) (.branch 60 (.branch 59 (.leaf (-7)) (.leaf (-6))) (.branch 61 (.leaf (-5)) (.leaf (-4))))),
  (.branch 61 (.leaf (-5)) (.leaf (-4))),
  (.branch 57 (.branch 54 (.branch 53 (.leaf (-20)) (.leaf (-18))) (.branch 55 (.leaf (-16)) (.branch 56 (.leaf (-14)) (.leaf (-12))))) (.branch 59 (.branch 58 (.leaf (-10)) (.leaf (-8))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2))))))]
def witnessD7_023_243 : CycleWitness 7 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (2))) (.branch 10 (.leaf (0)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (5))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (4)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (2)) (.leaf (6))) (.branch 22 (.leaf (3)) (.leaf (1))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (5)) (.leaf (1)))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (3))) (.branch 30 (.leaf (2)) (.leaf (4))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (3)) (.leaf (0))) (.branch 37 (.leaf (6)) (.leaf (1))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (5)) (.leaf (2))) (.branch 41 (.leaf (0)) (.leaf (3)))) (.branch 44 (.branch 43 (.leaf (1)) (.leaf (4))) (.branch 45 (.leaf (0)) (.leaf (2)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (3)) (.leaf (1))) (.branch 49 (.leaf (5)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (6))) (.branch 53 (.leaf (3)) (.leaf (1))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (2))) (.branch 57 (.leaf (4)) (.leaf (1)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (3))) (.branch 61 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_243
  counts := ![(.branch 28 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 45 (.branch 36 (.branch 32 (.leaf (7)) (.leaf (8))) (.branch 41 (.leaf (9)) (.leaf (10)))) (.branch 55 (.branch 50 (.leaf (11)) (.leaf (12))) (.branch 59 (.leaf (13)) (.leaf (14)))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 62 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 36 (.leaf (-8)) (.leaf (-9)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 27 (.branch 17 (.leaf (-18)) (.leaf (-19))) (.branch 58 (.leaf (-21)) (.leaf (-22))))),
  (.branch 30 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 34 (.leaf (-6)) (.branch 61 (.leaf (-9)) (.leaf (-10))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-7)) (.leaf (-9)))) (.branch 47 (.leaf (-10)) (.branch 53 (.leaf (-11)) (.leaf (-12))))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (-19)) (.leaf (-30)))),
  (.branch 49 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (-19)) (.leaf (-20))))]
  high := ![(.branch 60 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 61 (.leaf (-6)) (.leaf (-4)))),
  (.branch 60 (.branch 59 (.leaf (-22)) (.leaf (-17))) (.branch 61 (.leaf (-12)) (.leaf (-7)))),
  (.leaf (-10)),
  (.branch 54 (.leaf (-12)) (.branch 61 (.leaf (-10)) (.leaf (-7)))),
  (.branch 58 (.branch 32 (.branch 19 (.leaf (-30)) (.leaf (-29))) (.branch 45 (.leaf (-28)) (.leaf (-27)))) (.branch 60 (.branch 59 (.leaf (-23)) (.leaf (-19))) (.branch 61 (.leaf (-15)) (.leaf (-11))))),
  (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-4)) (.leaf (0)))),
  (.branch 57 (.branch 54 (.branch 53 (.leaf (-20)) (.leaf (-18))) (.branch 55 (.leaf (-16)) (.branch 56 (.leaf (-14)) (.leaf (-12))))) (.branch 59 (.branch 58 (.leaf (-10)) (.leaf (-8))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2))))))]
def witnessD7_023_244 : CycleWitness 7 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (6)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (5))) (.branch 22 (.leaf (3)) (.leaf (2))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (4)) (.leaf (0)))) (.branch 29 (.branch 28 (.leaf (2)) (.leaf (3))) (.branch 30 (.leaf (1)) (.leaf (6))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (5)) (.leaf (1)))) (.branch 44 (.branch 43 (.leaf (0)) (.leaf (3))) (.branch 45 (.leaf (2)) (.leaf (4)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (3)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (6))) (.branch 53 (.leaf (3)) (.leaf (1))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (0)) (.leaf (2))) (.branch 57 (.leaf (4)) (.leaf (0)))) (.branch 60 (.branch 59 (.leaf (1)) (.leaf (3))) (.branch 61 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_244
  counts := ![(.branch 27 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 54 (.leaf (9)) (.branch 59 (.leaf (10)) (.leaf (11)))))),
  (.branch 33 (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 51 (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))) (.branch 56 (.leaf (9)) (.branch 61 (.leaf (10)) (.leaf (11)))))),
  (.branch 29 (.branch 13 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 41 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-4)) (.branch 50 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.branch 30 (.leaf (-15)) (.leaf (-18)))),
  (.branch 33 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 61 (.leaf (-6)) (.leaf (-9)))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-6)))) (.branch 37 (.leaf (-8)) (.branch 53 (.leaf (-11)) (.leaf (-13))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (-4))) (.branch 46 (.leaf (-7)) (.leaf (-9)))),
  (.branch 41 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-32)))]
  high := ![(.branch 60 (.branch 59 (.leaf (-6)) (.leaf (-5))) (.branch 61 (.leaf (-4)) (.leaf (-3)))),
  (.branch 60 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 61 (.leaf (-13)) (.leaf (-9)))),
  (.leaf (-9)),
  (.branch 54 (.leaf (-13)) (.branch 61 (.leaf (-12)) (.leaf (-11)))),
  (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5))))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 56 (.branch 53 (.branch 11 (.leaf (-32)) (.branch 32 (.leaf (-31)) (.leaf (-30)))) (.branch 54 (.leaf (-27)) (.branch 55 (.leaf (-24)) (.leaf (-21))))) (.branch 59 (.branch 57 (.leaf (-18)) (.branch 58 (.leaf (-15)) (.leaf (-12)))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-6)) (.leaf (-3))))))]
def witnessD7_023_245 : CycleWitness 7 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (0)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (1)) (.leaf (6))) (.branch 18 (.leaf (0)) (.leaf (3)))) (.branch 21 (.branch 20 (.leaf (2)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (4))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (1)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (3)))) (.branch 29 (.branch 28 (.leaf (5)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (2))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (6)) (.leaf (1))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (4)) (.leaf (0))) (.branch 41 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 43 (.leaf (1)) (.leaf (0))) (.branch 45 (.leaf (2)) (.leaf (0)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (1)) (.leaf (5))) (.branch 49 (.leaf (0)) (.leaf (3)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (4))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (1)) (.leaf (2))) (.branch 57 (.leaf (0)) (.leaf (3)))) (.branch 60 (.branch 59 (.leaf (6)) (.leaf (1))) (.branch 61 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_245
  counts := ![(.branch 30 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 46 (.branch 36 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.branch 44 (.leaf (12)) (.leaf (13))))) (.branch 53 (.branch 49 (.leaf (14)) (.leaf (15))) (.branch 57 (.leaf (16)) (.branch 61 (.leaf (17)) (.leaf (18))))))),
  (.branch 29 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 43 (.leaf (9)) (.leaf (10)))) (.branch 55 (.branch 52 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 14 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-10)))) (.branch 46 (.branch 32 (.leaf (-12)) (.leaf (-14))) (.branch 49 (.leaf (-16)) (.leaf (-18))))),
  (.branch 24 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 55 (.leaf (-6)) (.leaf (-7)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 35 (.leaf (-6)) (.branch 45 (.leaf (-7)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (-15)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 54 (.branch 50 (.leaf (-18)) (.leaf (-17))) (.branch 58 (.leaf (-16)) (.leaf (-15)))),
  (.branch 56 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-4)))),
  (.branch 57 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-5)) (.branch 59 (.leaf (-2)) (.leaf (0))))),
  (.branch 51 (.branch 35 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17)))) (.branch 60 (.branch 59 (.leaf (-16)) (.leaf (-12))) (.branch 61 (.leaf (-8)) (.leaf (-4))))),
  (.branch 58 (.branch 56 (.branch 55 (.leaf (-16)) (.leaf (-14))) (.branch 57 (.leaf (-12)) (.leaf (-10)))) (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-6))) (.branch 61 (.leaf (-4)) (.leaf (-2))))),
  (.branch 55 (.branch 51 (.branch 49 (.leaf (-15)) (.branch 50 (.leaf (-14)) (.leaf (-13)))) (.branch 53 (.branch 52 (.leaf (-12)) (.leaf (-11))) (.branch 54 (.leaf (-10)) (.leaf (-9))))) (.branch 58 (.branch 56 (.leaf (-8)) (.branch 57 (.leaf (-7)) (.leaf (-6)))) (.branch 60 (.branch 59 (.leaf (-5)) (.leaf (-4))) (.branch 61 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 60 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 61 (.leaf (-3)) (.leaf (-2))))]
def witnessD7_023_246 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (4)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (2))) (.branch 22 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (5)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (1))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (2))) (.branch 37 (.leaf (0)) (.leaf (1))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (4)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (3)) (.leaf (1)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (1)) (.leaf (2))) (.branch 52 (.leaf (0)) (.leaf (1))))) (.branch 56 (.branch 54 (.leaf (0)) (.branch 55 (.leaf (6)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (3)) (.leaf (1))))))))
  code := certificateD7_246
  counts := ![(.branch 28 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 16 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))) (.branch 24 (.branch 22 (.leaf (10)) (.leaf (11))) (.branch 26 (.leaf (12)) (.leaf (13)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (14)) (.branch 32 (.leaf (15)) (.leaf (16)))) (.branch 39 (.branch 37 (.leaf (17)) (.leaf (18))) (.branch 41 (.leaf (19)) (.leaf (20))))) (.branch 52 (.branch 47 (.branch 46 (.leaf (21)) (.leaf (22))) (.branch 49 (.leaf (23)) (.leaf (24)))) (.branch 56 (.branch 54 (.leaf (25)) (.leaf (26))) (.branch 58 (.leaf (27)) (.leaf (28))))))),
  (.branch 30 (.branch 15 (.branch 5 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 45 (.branch 35 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 38 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 53 (.branch 48 (.leaf (15)) (.branch 50 (.leaf (16)) (.leaf (17)))) (.branch 57 (.leaf (18)) (.branch 60 (.leaf (19)) (.leaf (20))))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 55 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 19 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 4 (.leaf (-12)) (.branch 17 (.leaf (-13)) (.leaf (-14))))) (.branch 34 (.branch 32 (.leaf (-15)) (.leaf (-16))) (.branch 47 (.leaf (-17)) (.branch 49 (.leaf (-18)) (.leaf (-19)))))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-35))),
  (.branch 55 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 50 (.leaf (-19)) (.branch 59 (.leaf (-18)) (.leaf (-13)))),
  (.branch 54 (.leaf (-1)) (.leaf (0))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-35)) (.leaf (-34))) (.branch 28 (.leaf (-33)) (.leaf (-32)))) (.branch 31 (.branch 30 (.leaf (-31)) (.leaf (-30))) (.branch 32 (.leaf (-29)) (.leaf (-28))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))))) (.branch 51 (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_023_247 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (4)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (2)) (.branch 22 (.leaf (0)) (.leaf (3))))) (.branch 27 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (5))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 35 (.leaf (2)) (.branch 37 (.leaf (0)) (.leaf (3))))) (.branch 42 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (4)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (0)))) (.branch 50 (.leaf (2)) (.branch 52 (.leaf (0)) (.leaf (3))))) (.branch 57 (.branch 54 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.leaf (2)) (.branch 59 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_247
  counts := ![(.branch 29 (.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (9)) (.leaf (10))) (.branch 19 (.leaf (11)) (.leaf (12)))) (.branch 24 (.branch 22 (.leaf (13)) (.leaf (14))) (.branch 26 (.leaf (15)) (.branch 27 (.leaf (16)) (.leaf (17))))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (18)) (.leaf (19))) (.branch 34 (.leaf (20)) (.leaf (21)))) (.branch 39 (.branch 37 (.leaf (22)) (.leaf (23))) (.branch 41 (.leaf (24)) (.branch 42 (.leaf (25)) (.leaf (26)))))) (.branch 52 (.branch 47 (.branch 46 (.leaf (27)) (.leaf (28))) (.branch 49 (.leaf (29)) (.branch 51 (.leaf (30)) (.leaf (31))))) (.branch 56 (.branch 54 (.leaf (32)) (.leaf (33))) (.branch 57 (.leaf (34)) (.branch 59 (.leaf (35)) (.leaf (36)))))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 60 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.branch 30 (.leaf (0)) (.leaf (-30))),
  (.leaf (0))]
  high := ![(.branch 58 (.leaf (-4)) (.leaf (-3))),
  (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 51 (.leaf (-5)) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28)))) (.branch 35 (.branch 34 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-25)) (.leaf (-24))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.leaf (-20)))) (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_023_248 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (4)) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (1))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (5)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (2))) (.branch 44 (.leaf (0)) (.leaf (1)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.leaf (6)) (.branch 55 (.leaf (0)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (0)) (.leaf (1))))))))
  code := certificateD7_248
  counts := ![(.branch 29 (.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.leaf (15)))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (16)) (.leaf (17))) (.branch 34 (.leaf (18)) (.leaf (19)))) (.branch 40 (.branch 38 (.leaf (20)) (.leaf (21))) (.branch 42 (.leaf (22)) (.leaf (23))))) (.branch 51 (.branch 47 (.branch 46 (.leaf (24)) (.leaf (25))) (.branch 49 (.leaf (26)) (.leaf (27)))) (.branch 55 (.branch 53 (.leaf (28)) (.leaf (29))) (.branch 57 (.leaf (30)) (.branch 59 (.leaf (31)) (.leaf (32)))))))),
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-51))),
  (.branch 24 (.leaf (0)) (.leaf (-36))),
  (.branch 39 (.leaf (0)) (.leaf (-21))),
  (.branch 54 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 52 (.branch 48 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 56 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))),
  (.branch 53 (.branch 49 (.leaf (-3)) (.leaf (-2))) (.branch 57 (.leaf (-1)) (.leaf (0)))),
  (.branch 51 (.leaf (-5)) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 34 (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-51)) (.branch 11 (.leaf (-50)) (.leaf (-49)))) (.branch 13 (.leaf (-48)) (.branch 14 (.leaf (-47)) (.leaf (-46))))) (.branch 18 (.branch 16 (.leaf (-45)) (.branch 17 (.leaf (-44)) (.leaf (-43)))) (.branch 19 (.leaf (-42)) (.branch 20 (.leaf (-41)) (.leaf (-40)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-39)) (.branch 23 (.leaf (-38)) (.leaf (-37)))) (.branch 25 (.leaf (-36)) (.branch 26 (.leaf (-35)) (.leaf (-34))))) (.branch 30 (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))) (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.leaf (-27))))))) (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-36)) (.leaf (-35))) (.branch 27 (.leaf (-34)) (.leaf (-33)))) (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))))) (.branch 51 (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 44 (.branch 41 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17))))) (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_023_249 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 23 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (1))))))) (.branch 45 (.branch 37 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (0)) (.leaf (1))))) (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (5)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 53 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 52 (.leaf (0)) (.leaf (1))))) (.branch 56 (.branch 54 (.leaf (0)) (.branch 55 (.leaf (2)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (6)) (.leaf (1))))))))
  code := certificateD7_249
  counts := ![(.branch 28 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 21 (.branch 16 (.branch 14 (.leaf (7)) (.leaf (8))) (.branch 18 (.leaf (9)) (.leaf (10)))) (.branch 24 (.branch 22 (.leaf (11)) (.leaf (12))) (.branch 26 (.leaf (13)) (.leaf (14)))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (15)) (.leaf (16))) (.branch 34 (.leaf (17)) (.leaf (18)))) (.branch 41 (.branch 38 (.leaf (19)) (.leaf (20))) (.branch 42 (.leaf (21)) (.leaf (22))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (23)) (.leaf (24))) (.branch 51 (.leaf (25)) (.leaf (26)))) (.branch 56 (.branch 54 (.leaf (27)) (.leaf (28))) (.branch 58 (.leaf (29)) (.leaf (30))))))),
  (.branch 30 (.branch 13 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 47 (.branch 37 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.branch 43 (.leaf (12)) (.leaf (13))))) (.branch 53 (.branch 50 (.leaf (14)) (.leaf (15))) (.branch 57 (.leaf (16)) (.branch 60 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 59 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 19 (.leaf (0)) (.leaf (-41))),
  (.branch 39 (.leaf (0)) (.leaf (-21))),
  (.branch 59 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 54 (.leaf (-1)) (.leaf (0))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (-41)) (.leaf (-40))) (.branch 22 (.leaf (-39)) (.branch 23 (.leaf (-38)) (.leaf (-37))))) (.branch 26 (.branch 25 (.leaf (-36)) (.leaf (-35))) (.branch 27 (.leaf (-34)) (.branch 28 (.leaf (-33)) (.leaf (-32)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-31)) (.leaf (-30))) (.branch 32 (.leaf (-29)) (.branch 33 (.leaf (-28)) (.leaf (-27))))) (.branch 36 (.branch 35 (.leaf (-26)) (.leaf (-25))) (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22))))))) (.branch 49 (.branch 44 (.branch 41 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17))))) (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 44 (.branch 41 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17))))) (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_023_250 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (4)) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (5)) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (0)) (.leaf (1))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (4)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (3))) (.branch 44 (.leaf (0)) (.leaf (1)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.leaf (6)) (.branch 55 (.leaf (0)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (0)) (.leaf (1))))))))
  code := certificateD7_250
  counts := ![(.branch 29 (.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.leaf (15)))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (16)) (.leaf (17))) (.branch 34 (.leaf (18)) (.leaf (19)))) (.branch 40 (.branch 38 (.leaf (20)) (.leaf (21))) (.branch 42 (.leaf (22)) (.leaf (23))))) (.branch 51 (.branch 47 (.branch 46 (.leaf (24)) (.leaf (25))) (.branch 49 (.leaf (26)) (.leaf (27)))) (.branch 55 (.branch 53 (.leaf (28)) (.leaf (29))) (.branch 57 (.leaf (30)) (.branch 59 (.leaf (31)) (.leaf (32)))))))),
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-21))),
  (.branch 24 (.leaf (0)) (.leaf (-36))),
  (.branch 54 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 52 (.branch 48 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 56 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))),
  (.branch 53 (.branch 49 (.leaf (-3)) (.leaf (-2))) (.branch 57 (.leaf (-1)) (.leaf (0)))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 49 (.branch 44 (.branch 41 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17))))) (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-36)) (.leaf (-35))) (.branch 27 (.leaf (-34)) (.leaf (-33)))) (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))))) (.branch 51 (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_023_251 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (4)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (5)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (6))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (4)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (0)) (.leaf (5)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (0)) (.leaf (3)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (6)) (.leaf (0))))) (.branch 56 (.branch 54 (.leaf (1)) (.branch 55 (.leaf (0)) (.leaf (4)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (5))))))))
  code := certificateD7_251
  counts := ![(.branch 29 (.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.leaf (15)))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (16)) (.leaf (17))) (.branch 34 (.leaf (18)) (.leaf (19)))) (.branch 40 (.branch 38 (.leaf (20)) (.leaf (21))) (.branch 42 (.leaf (22)) (.leaf (23))))) (.branch 51 (.branch 47 (.branch 46 (.leaf (24)) (.leaf (25))) (.branch 49 (.leaf (26)) (.leaf (27)))) (.branch 55 (.branch 53 (.leaf (28)) (.leaf (29))) (.branch 57 (.leaf (30)) (.branch 59 (.leaf (31)) (.leaf (32)))))))),
  (.branch 28 (.branch 13 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (-14))) (.branch 45 (.leaf (-16)) (.leaf (-18)))),
  (.branch 15 (.leaf (0)) (.branch 56 (.leaf (-6)) (.leaf (-7)))),
  (.branch 41 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.branch 30 (.leaf (-10)) (.leaf (-12))))]
  high := ![(.branch 52 (.branch 48 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 56 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-17)) (.leaf (-16)))) (.branch 50 (.branch 49 (.leaf (-15)) (.leaf (-14))) (.branch 51 (.leaf (-13)) (.leaf (-12))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.leaf (-8)))) (.branch 58 (.branch 57 (.leaf (-7)) (.leaf (-6))) (.branch 59 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 58 (.branch 57 (.leaf (-7)) (.leaf (-6))) (.branch 59 (.leaf (-5)) (.leaf (-4)))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 55 (.branch 53 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 54 (.leaf (-10)) (.leaf (-9)))) (.branch 57 (.branch 56 (.leaf (-8)) (.leaf (-7))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-5)) (.leaf (-4))))))]
def witnessD7_023_252 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (6)) (.leaf (0))) (.branch 22 (.leaf (4)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (3))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (5)) (.leaf (0))) (.branch 37 (.leaf (2)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (0)) (.leaf (4)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (6)) (.leaf (0))) (.branch 52 (.leaf (3)) (.leaf (0))))) (.branch 56 (.branch 54 (.leaf (1)) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_252
  counts := ![(.branch 29 (.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.leaf (15)))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (16)) (.leaf (17))) (.branch 34 (.leaf (18)) (.leaf (19)))) (.branch 40 (.branch 38 (.leaf (20)) (.leaf (21))) (.branch 42 (.leaf (22)) (.leaf (23))))) (.branch 51 (.branch 47 (.branch 46 (.leaf (24)) (.leaf (25))) (.branch 49 (.leaf (26)) (.leaf (27)))) (.branch 55 (.branch 53 (.leaf (28)) (.leaf (29))) (.branch 57 (.leaf (30)) (.branch 59 (.leaf (31)) (.leaf (32)))))))),
  (.branch 28 (.branch 13 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (-7))) (.branch 45 (.leaf (-12)) (.leaf (-15)))),
  (.branch 11 (.leaf (0)) (.branch 30 (.leaf (-10)) (.leaf (-12)))),
  (.branch 41 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-25))),
  (.branch 20 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 52 (.branch 48 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 56 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-10)) (.leaf (-8))))),
  (.branch 55 (.branch 53 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 54 (.leaf (-10)) (.leaf (-9)))) (.branch 57 (.branch 56 (.leaf (-8)) (.leaf (-7))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 47 (.branch 41 (.branch 38 (.branch 36 (.leaf (-25)) (.branch 37 (.leaf (-24)) (.leaf (-23)))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))) (.branch 44 (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17)))) (.branch 45 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_023_253 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (4)) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (3)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (3)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (5)) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (3))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (3)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (4)) (.branch 40 (.leaf (0)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (0)) (.leaf (3)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (2)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (1)) (.leaf (0))) (.branch 52 (.leaf (3)) (.leaf (0))))) (.branch 56 (.branch 54 (.leaf (6)) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_253
  counts := ![(.branch 29 (.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.leaf (15)))))) (.branch 44 (.branch 36 (.branch 32 (.branch 31 (.leaf (16)) (.leaf (17))) (.branch 34 (.leaf (18)) (.leaf (19)))) (.branch 40 (.branch 38 (.leaf (20)) (.leaf (21))) (.branch 42 (.leaf (22)) (.leaf (23))))) (.branch 51 (.branch 47 (.branch 46 (.leaf (24)) (.leaf (25))) (.branch 49 (.leaf (26)) (.leaf (27)))) (.branch 55 (.branch 53 (.leaf (28)) (.leaf (29))) (.branch 57 (.leaf (30)) (.branch 59 (.leaf (31)) (.leaf (32)))))))),
  (.branch 28 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-21))),
  (.branch 24 (.leaf (0)) (.leaf (-36))),
  (.branch 54 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 52 (.branch 48 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 56 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))),
  (.branch 51 (.leaf (-5)) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 57 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 49 (.branch 44 (.branch 41 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17))))) (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-36)) (.leaf (-35))) (.branch 27 (.leaf (-34)) (.leaf (-33)))) (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))))) (.branch 51 (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_023_254 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (3))) (.branch 22 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (1))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (3))) (.branch 37 (.leaf (0)) (.leaf (6))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (0))) (.branch 44 (.leaf (4)) (.leaf (1)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (5)) (.leaf (0)))) (.branch 51 (.branch 50 (.leaf (1)) (.leaf (3))) (.branch 52 (.leaf (0)) (.leaf (2))))) (.branch 56 (.branch 54 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (6)) (.leaf (0))) (.branch 59 (.leaf (4)) (.leaf (1))))))))
  code := certificateD7_254
  counts := ![(.branch 28 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 16 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))) (.branch 24 (.branch 22 (.leaf (10)) (.leaf (11))) (.branch 26 (.leaf (12)) (.leaf (13)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (14)) (.branch 32 (.leaf (15)) (.leaf (16)))) (.branch 39 (.branch 37 (.leaf (17)) (.leaf (18))) (.branch 41 (.leaf (19)) (.leaf (20))))) (.branch 52 (.branch 47 (.branch 46 (.leaf (21)) (.leaf (22))) (.branch 49 (.leaf (23)) (.leaf (24)))) (.branch 56 (.branch 54 (.leaf (25)) (.leaf (26))) (.branch 58 (.leaf (27)) (.leaf (28))))))),
  (.branch 30 (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 19 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 4 (.leaf (-12)) (.branch 17 (.leaf (-13)) (.leaf (-14))))) (.branch 34 (.branch 32 (.leaf (-15)) (.leaf (-16))) (.branch 47 (.leaf (-17)) (.branch 49 (.leaf (-18)) (.leaf (-19)))))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-12)) (.leaf (-13)))),
  (.branch 18 (.leaf (0)) (.branch 57 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 50 (.leaf (-19)) (.branch 59 (.leaf (-18)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 56 (.branch 54 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 53 (.branch 50 (.branch 28 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_023_255 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (5)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (1))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (3)) (.leaf (1)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (0)) (.leaf (4)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (2)) (.leaf (1)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (3)) (.leaf (1)))) (.branch 51 (.branch 50 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (0))))) (.branch 56 (.branch 54 (.leaf (1)) (.branch 55 (.leaf (0)) (.leaf (6)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_255
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 23 (.leaf (9)) (.branch 25 (.leaf (10)) (.leaf (11)))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14)))) (.branch 38 (.leaf (15)) (.branch 40 (.leaf (16)) (.leaf (17))))) (.branch 50 (.branch 46 (.leaf (18)) (.branch 47 (.leaf (19)) (.leaf (20)))) (.branch 55 (.branch 53 (.leaf (21)) (.leaf (22))) (.branch 58 (.leaf (23)) (.leaf (24))))))),
  (.branch 30 (.branch 15 (.branch 6 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 45 (.branch 36 (.branch 34 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 54 (.branch 49 (.leaf (15)) (.branch 51 (.leaf (16)) (.leaf (17)))) (.branch 57 (.leaf (18)) (.branch 60 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))) (.branch 32 (.leaf (-19)) (.branch 47 (.leaf (-22)) (.leaf (-25))))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-19))),
  (.branch 26 (.leaf (0)) (.leaf (-34))),
  (.branch 56 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 56 (.branch 48 (.leaf (-25)) (.leaf (-24))) (.branch 59 (.leaf (-22)) (.leaf (-17)))),
  (.leaf (0)),
  (.leaf (-2)),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.branch 45 (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-34)) (.leaf (-33))) (.branch 29 (.leaf (-32)) (.leaf (-31)))) (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.leaf (-27))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-26)) (.leaf (-25))) (.branch 37 (.leaf (-24)) (.leaf (-23)))) (.branch 40 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18))))))) (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_023_256 : CycleWitness 7 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (6))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (2)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (1)))) (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (1)) (.leaf (3))))) (.branch 26 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (2)) (.leaf (1))))))) (.branch 45 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (4)) (.leaf (1)))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (1)) (.leaf (5))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (2)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (3))) (.branch 44 (.leaf (2)) (.leaf (1)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (6)) (.leaf (1)))) (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (1)) (.leaf (4))))) (.branch 56 (.branch 54 (.leaf (0)) (.branch 55 (.leaf (2)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (5))) (.branch 59 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_256
  counts := ![(.branch 27 (.branch 12 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 42 (.branch 32 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 36 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 51 (.branch 46 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 54 (.leaf (18)) (.branch 57 (.leaf (19)) (.leaf (20))))))),
  (.branch 30 (.branch 15 (.branch 7 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 29 (.branch 14 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-9)) (.leaf (-18)))) (.branch 32 (.leaf (-23)) (.branch 47 (.leaf (-28)) (.leaf (-33))))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 58 (.branch 48 (.leaf (-33)) (.leaf (-32))) (.branch 59 (.leaf (-28)) (.leaf (-24)))),
  (.branch 53 (.leaf (-2)) (.branch 57 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_023 : Fin 16 → CycleWitness 7 := ![witnessD7_023_241, witnessD7_023_242, witnessD7_023_243, witnessD7_023_244, witnessD7_023_245, witnessD7_023_246, witnessD7_023_247, witnessD7_023_248, witnessD7_023_249, witnessD7_023_250, witnessD7_023_251, witnessD7_023_252, witnessD7_023_253, witnessD7_023_254, witnessD7_023_255, witnessD7_023_256]
end RealPinwheel.FiveSixths


