-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_271
-- name    : RealPinwheel_FiveSixths_WitnessP9_271
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:07:44.704979+00:00
-- url     : https://prove2.me/theorems/0d468a48-c7ed-492e-ba32-74dbd9325f21
-- title:
--   Exact witness block P9_271
-- statement:
--   These exact witnesses represent words 4157 through 4194 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 4157–4194; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_271_4156 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (7)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (8))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (4)) (.leaf (1))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (5)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (6))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (7)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (8))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (3)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (4))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (5)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (6)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (7)) (.leaf (0))) (.branch 46 (.leaf (8)) (.branch 47 (.leaf (1)) (.leaf (0)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (3)) (.leaf (0))) (.branch 51 (.leaf (2)) (.branch 52 (.leaf (4)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (5))) (.branch 56 (.leaf (0)) (.branch 57 (.leaf (6)) (.leaf (0))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (7)) (.leaf (1))) (.branch 61 (.leaf (0)) (.branch 62 (.leaf (8)) (.leaf (0))))) (.branch 65 (.branch 64 (.leaf (2)) (.leaf (3))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (1)) (.leaf (4)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (0)) (.leaf (5))) (.branch 71 (.leaf (0)) (.branch 72 (.leaf (6)) (.leaf (1))))) (.branch 75 (.branch 74 (.leaf (0)) (.leaf (7))) (.branch 76 (.leaf (0)) (.branch 77 (.leaf (2)) (.leaf (8)))))))))
  code := certificateP9_4156
  counts := ![(.branch 37 (.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 22 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 32 (.branch 30 (.leaf (11)) (.leaf (12))) (.branch 35 (.leaf (13)) (.leaf (14)))))) (.branch 58 (.branch 48 (.branch 43 (.branch 40 (.leaf (15)) (.leaf (16))) (.branch 45 (.leaf (17)) (.leaf (18)))) (.branch 53 (.branch 50 (.leaf (19)) (.leaf (20))) (.branch 56 (.leaf (21)) (.leaf (22))))) (.branch 69 (.branch 63 (.branch 61 (.leaf (23)) (.leaf (24))) (.branch 66 (.leaf (25)) (.leaf (26)))) (.branch 74 (.branch 71 (.leaf (27)) (.leaf (28))) (.branch 76 (.leaf (29)) (.leaf (30))))))),
  (.branch 34 (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 54 (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))) (.branch 67 (.branch 60 (.leaf (9)) (.leaf (10))) (.branch 73 (.leaf (11)) (.leaf (12)))))),
  (.branch 38 (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 64 (.branch 51 (.leaf (3)) (.leaf (4))) (.branch 77 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 3 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 65 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 68 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 55 (.leaf (3)) (.branch 70 (.leaf (4)) (.leaf (5))))),
  (.branch 42 (.branch 10 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 57 (.leaf (3)) (.branch 72 (.leaf (4)) (.leaf (5))))),
  (.branch 44 (.branch 13 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 59 (.leaf (3)) (.branch 75 (.leaf (4)) (.leaf (5))))),
  (.branch 46 (.branch 16 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))) (.branch 62 (.leaf (3)) (.branch 78 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 11 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (-38))) (.branch 33 (.leaf (-40)) (.leaf (-42)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (-32)) (.leaf (-34)))),
  (.branch 7 (.leaf (0)) (.leaf (-26))),
  (.branch 10 (.leaf (0)) (.branch 72 (.leaf (-17)) (.leaf (-19)))),
  (.branch 44 (.branch 13 (.leaf (0)) (.leaf (-8))) (.branch 59 (.leaf (-9)) (.leaf (-11)))),
  (.branch 31 (.leaf (0)) (.branch 46 (.leaf (-1)) (.leaf (-3))))]
  high := ![(.branch 77 (.leaf (-10)) (.leaf (-5))),
  (.branch 75 (.branch 74 (.leaf (-10)) (.leaf (-8))) (.branch 76 (.leaf (-6)) (.branch 77 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-1)),
  (.branch 70 (.branch 66 (.branch 34 (.leaf (-42)) (.branch 50 (.leaf (-41)) (.leaf (-40)))) (.branch 68 (.branch 67 (.leaf (-37)) (.leaf (-34))) (.branch 69 (.leaf (-31)) (.leaf (-28))))) (.branch 74 (.branch 72 (.branch 71 (.leaf (-25)) (.leaf (-22))) (.branch 73 (.leaf (-19)) (.leaf (-16)))) (.branch 76 (.branch 75 (.leaf (-13)) (.leaf (-10))) (.branch 77 (.leaf (-7)) (.leaf (-4)))))),
  (.branch 71 (.branch 53 (.branch 21 (.leaf (-34)) (.branch 37 (.leaf (-33)) (.leaf (-32)))) (.branch 69 (.leaf (-31)) (.branch 70 (.leaf (-28)) (.leaf (-25))))) (.branch 74 (.branch 72 (.leaf (-22)) (.branch 73 (.leaf (-19)) (.leaf (-16)))) (.branch 76 (.branch 75 (.leaf (-13)) (.leaf (-10))) (.branch 77 (.leaf (-7)) (.leaf (-4)))))),
  (.branch 73 (.branch 71 (.branch 8 (.leaf (-26)) (.leaf (-25))) (.branch 72 (.leaf (-22)) (.leaf (-19)))) (.branch 75 (.branch 74 (.leaf (-16)) (.leaf (-13))) (.branch 76 (.leaf (-10)) (.branch 77 (.leaf (-7)) (.leaf (-4)))))),
  (.branch 75 (.branch 73 (.leaf (-19)) (.branch 74 (.leaf (-16)) (.leaf (-13)))) (.branch 76 (.leaf (-10)) (.branch 77 (.leaf (-7)) (.leaf (-4))))),
  (.branch 76 (.branch 60 (.leaf (-11)) (.leaf (-10))) (.branch 77 (.leaf (-7)) (.leaf (-4)))),
  (.branch 47 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (0))))]
def witnessP9_271_4157 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (4))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (7)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (3)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (4))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (8))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (4))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (7)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (5))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (2)) (.leaf (0))))) (.branch 36 (.branch 35 (.leaf (4)) (.leaf (0))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (6)) (.leaf (8)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (2))) (.branch 42 (.leaf (3)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (5)) (.leaf (4))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (7)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (6)) (.branch 52 (.leaf (3)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (4))) (.branch 56 (.leaf (0)) (.branch 57 (.leaf (5)) (.leaf (8))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (2)) (.leaf (0))) (.branch 61 (.leaf (3)) (.branch 62 (.leaf (0)) (.leaf (1))))) (.branch 65 (.branch 64 (.leaf (6)) (.leaf (4))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (2)) (.leaf (7)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (0)) (.leaf (5))) (.branch 71 (.leaf (3)) (.branch 72 (.leaf (1)) (.leaf (0))))) (.branch 75 (.branch 74 (.leaf (4)) (.leaf (0))) (.branch 76 (.leaf (2)) (.branch 77 (.leaf (6)) (.leaf (8)))))))))
  code := certificateP9_4157
  counts := ![(.branch 36 (.branch 17 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 30 (.leaf (9)) (.branch 34 (.leaf (10)) (.leaf (11)))))) (.branch 56 (.branch 47 (.branch 40 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14)))) (.branch 49 (.leaf (15)) (.branch 53 (.leaf (16)) (.leaf (17))))) (.branch 66 (.branch 60 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20)))) (.branch 73 (.branch 69 (.leaf (21)) (.leaf (22))) (.branch 75 (.leaf (23)) (.leaf (24))))))),
  (.branch 37 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 46 (.leaf (5)) (.leaf (6))) (.branch 63 (.leaf (7)) (.branch 72 (.leaf (8)) (.leaf (9)))))),
  (.branch 41 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))) (.branch 59 (.branch 50 (.leaf (5)) (.leaf (6))) (.branch 67 (.leaf (7)) (.branch 76 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.branch 71 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 55 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 65 (.leaf (6)) (.branch 74 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 70 (.leaf (5)) (.leaf (6))))),
  (.branch 38 (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 64 (.branch 51 (.leaf (3)) (.leaf (4))) (.branch 77 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 68 (.leaf (3)) (.leaf (4))))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.branch 78 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 23 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-10)))) (.branch 49 (.branch 36 (.leaf (-11)) (.leaf (-12))) (.branch 62 (.leaf (-13)) (.branch 75 (.leaf (-14)) (.leaf (-15)))))),
  (.branch 2 (.leaf (0)) (.leaf (-20))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-27)) (.leaf (-29)))),
  (.branch 6 (.leaf (0)) (.branch 35 (.leaf (-15)) (.leaf (-16)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-21))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 76 (.leaf (-15)) (.branch 77 (.leaf (-12)) (.leaf (-9)))),
  (.branch 74 (.branch 64 (.branch 55 (.leaf (-20)) (.leaf (-19))) (.branch 73 (.leaf (-18)) (.leaf (-15)))) (.branch 76 (.branch 75 (.leaf (-12)) (.leaf (-9))) (.branch 77 (.leaf (-6)) (.leaf (-3))))),
  (.branch 68 (.leaf (-7)) (.branch 77 (.leaf (-6)) (.leaf (-3)))),
  (.branch 74 (.branch 72 (.branch 62 (.leaf (-29)) (.leaf (-28))) (.branch 73 (.leaf (-24)) (.leaf (-20)))) (.branch 76 (.branch 75 (.leaf (-16)) (.leaf (-12))) (.branch 77 (.leaf (-8)) (.leaf (-4))))),
  (.branch 76 (.branch 75 (.leaf (-16)) (.leaf (-12))) (.branch 77 (.leaf (-8)) (.leaf (-4)))),
  (.branch 74 (.branch 72 (.branch 71 (.leaf (-8)) (.leaf (-7))) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 72 (.branch 69 (.branch 49 (.leaf (-21)) (.leaf (-20))) (.branch 70 (.leaf (-18)) (.branch 71 (.leaf (-16)) (.leaf (-14))))) (.branch 75 (.branch 73 (.leaf (-12)) (.branch 74 (.leaf (-10)) (.leaf (-8)))) (.branch 76 (.leaf (-6)) (.branch 77 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 59 (.leaf (-1)) (.leaf (0)))]
def witnessP9_271_4158 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (2))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (7))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (5)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (3))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (8)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (4))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (6))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (7))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (0)) (.leaf (4))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (8)) (.branch 38 (.leaf (0)) (.leaf (5)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (2))) (.branch 42 (.leaf (3)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (6)) (.leaf (1))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (0)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (2)) (.leaf (7))) (.branch 51 (.leaf (0)) (.branch 52 (.leaf (5)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (3))) (.branch 56 (.leaf (0)) (.branch 57 (.leaf (8)) (.leaf (2))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (0)) (.leaf (4))) (.branch 61 (.leaf (0)) (.branch 62 (.leaf (1)) (.leaf (6))))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (5))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (2)) (.leaf (3)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (0)) (.leaf (7))) (.branch 71 (.leaf (1)) (.branch 72 (.leaf (0)) (.leaf (4))))) (.branch 75 (.branch 74 (.leaf (0)) (.leaf (2))) (.branch 76 (.leaf (8)) (.branch 77 (.leaf (0)) (.leaf (5)))))))))
  code := certificateP9_4158
  counts := ![(.branch 38 (.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (7)) (.leaf (8))) (.branch 25 (.leaf (9)) (.leaf (10)))) (.branch 33 (.branch 30 (.leaf (11)) (.leaf (12))) (.branch 35 (.leaf (13)) (.leaf (14)))))) (.branch 59 (.branch 48 (.branch 43 (.branch 40 (.leaf (15)) (.leaf (16))) (.branch 46 (.leaf (17)) (.leaf (18)))) (.branch 53 (.branch 51 (.leaf (19)) (.leaf (20))) (.branch 56 (.leaf (21)) (.leaf (22))))) (.branch 69 (.branch 64 (.branch 61 (.leaf (23)) (.leaf (24))) (.branch 66 (.leaf (25)) (.leaf (26)))) (.branch 74 (.branch 72 (.leaf (27)) (.leaf (28))) (.branch 77 (.leaf (29)) (.leaf (30))))))),
  (.branch 36 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 45 (.leaf (5)) (.leaf (6))) (.branch 62 (.leaf (7)) (.branch 71 (.leaf (8)) (.leaf (9)))))),
  (.branch 41 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))) (.branch 58 (.branch 49 (.leaf (5)) (.leaf (6))) (.branch 67 (.leaf (7)) (.branch 75 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 60 (.branch 47 (.leaf (3)) (.leaf (4))) (.branch 73 (.leaf (5)) (.leaf (6))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 65 (.branch 52 (.leaf (3)) (.leaf (4))) (.branch 78 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 70 (.leaf (3)) (.leaf (4))))),
  (.branch 37 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.branch 76 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-20)) (.leaf (-22)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-29)) (.leaf (-30)))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 18 (.leaf (0)) (.branch 37 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 67 (.leaf (-8)) (.branch 75 (.leaf (-7)) (.leaf (-5)))),
  (.branch 74 (.branch 72 (.branch 63 (.leaf (-22)) (.leaf (-21))) (.branch 73 (.leaf (-18)) (.leaf (-15)))) (.branch 76 (.branch 75 (.leaf (-12)) (.leaf (-9))) (.branch 77 (.leaf (-6)) (.leaf (-3))))),
  (.branch 76 (.leaf (-9)) (.branch 77 (.leaf (-6)) (.leaf (-3)))),
  (.branch 73 (.branch 70 (.branch 69 (.leaf (-10)) (.leaf (-9))) (.branch 71 (.leaf (-8)) (.branch 72 (.leaf (-7)) (.leaf (-6))))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 70 (.branch 66 (.branch 64 (.leaf (-30)) (.branch 65 (.leaf (-28)) (.leaf (-26)))) (.branch 68 (.branch 67 (.leaf (-24)) (.leaf (-22))) (.branch 69 (.leaf (-20)) (.leaf (-18))))) (.branch 74 (.branch 72 (.branch 71 (.leaf (-16)) (.leaf (-14))) (.branch 73 (.leaf (-12)) (.leaf (-10)))) (.branch 76 (.branch 75 (.leaf (-8)) (.leaf (-6))) (.branch 77 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 73 (.branch 71 (.branch 51 (.leaf (-17)) (.leaf (-16))) (.branch 72 (.leaf (-14)) (.leaf (-12)))) (.branch 75 (.branch 74 (.leaf (-10)) (.leaf (-8))) (.branch 76 (.leaf (-6)) (.branch 77 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 77 (.leaf (-4)) (.leaf (-2)))]
def witnessP9_271_4159 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (3)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (4))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (8)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (5)) (.leaf (1))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (6))))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (4))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (5)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (7))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (4))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (6)) (.leaf (5)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (1)) (.leaf (0))) (.branch 42 (.leaf (3)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (8)) (.leaf (0))) (.branch 46 (.leaf (4)) (.branch 47 (.leaf (1)) (.leaf (5)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (6))) (.branch 51 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (4))) (.branch 56 (.leaf (0)) (.branch 57 (.leaf (7)) (.leaf (5))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (0)) (.leaf (2))) (.branch 61 (.leaf (1)) (.branch 62 (.leaf (3)) (.leaf (0))))) (.branch 65 (.branch 64 (.leaf (6)) (.leaf (4))) (.branch 66 (.leaf (1)) (.branch 67 (.leaf (0)) (.leaf (5)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (2)) (.leaf (8))) (.branch 71 (.leaf (0)) (.branch 72 (.leaf (3)) (.leaf (1))))) (.branch 75 (.branch 74 (.leaf (4)) (.leaf (0))) (.branch 76 (.leaf (6)) (.branch 77 (.leaf (2)) (.leaf (5)))))))))
  code := certificateP9_4159
  counts := ![(.branch 37 (.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))) (.branch 56 (.branch 45 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 49 (.leaf (13)) (.branch 53 (.leaf (14)) (.leaf (15))))) (.branch 67 (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18)))) (.branch 71 (.leaf (19)) (.branch 75 (.leaf (20)) (.leaf (21))))))),
  (.branch 35 (.branch 14 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 54 (.branch 40 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))) (.branch 66 (.branch 61 (.leaf (9)) (.leaf (10))) (.branch 73 (.leaf (11)) (.leaf (12)))))),
  (.branch 43 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))) (.branch 60 (.branch 51 (.leaf (5)) (.leaf (6))) (.branch 69 (.leaf (7)) (.branch 77 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.branch 72 (.leaf (7)) (.leaf (8)))))),
  (.branch 36 (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 55 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 65 (.leaf (6)) (.branch 74 (.leaf (7)) (.leaf (8)))))),
  (.branch 39 (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 58 (.branch 48 (.leaf (4)) (.leaf (5))) (.branch 68 (.leaf (6)) (.branch 78 (.leaf (7)) (.leaf (8)))))),
  (.branch 38 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 64 (.branch 50 (.leaf (3)) (.leaf (4))) (.branch 76 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 70 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-14)) (.leaf (-18)))) (.branch 33 (.leaf (-22)) (.branch 59 (.leaf (-25)) (.leaf (-28))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.leaf (-14))) (.branch 40 (.leaf (-18)) (.branch 66 (.leaf (-20)) (.leaf (-22))))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-34)) (.leaf (-37)))),
  (.branch 6 (.leaf (0)) (.branch 74 (.leaf (-19)) (.leaf (-22)))),
  (.branch 29 (.leaf (0)) (.branch 48 (.leaf (-2)) (.leaf (-5)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 68 (.branch 60 (.leaf (-28)) (.branch 64 (.leaf (-27)) (.leaf (-26)))) (.branch 76 (.branch 72 (.leaf (-25)) (.leaf (-24))) (.branch 77 (.leaf (-19)) (.leaf (-14))))),
  (.branch 75 (.branch 67 (.leaf (-22)) (.branch 74 (.leaf (-21)) (.leaf (-18)))) (.branch 76 (.leaf (-15)) (.branch 77 (.leaf (-12)) (.leaf (-9))))),
  (.leaf (-3)),
  (.branch 63 (.branch 33 (.branch 23 (.leaf (-37)) (.leaf (-36))) (.branch 43 (.leaf (-35)) (.branch 53 (.leaf (-34)) (.leaf (-33))))) (.branch 75 (.branch 73 (.leaf (-32)) (.branch 74 (.leaf (-27)) (.leaf (-22)))) (.branch 76 (.leaf (-17)) (.branch 77 (.leaf (-12)) (.leaf (-7)))))),
  (.branch 76 (.branch 75 (.leaf (-22)) (.leaf (-17))) (.branch 77 (.leaf (-12)) (.leaf (-7)))),
  (.branch 59 (.branch 49 (.leaf (-5)) (.leaf (-4))) (.branch 69 (.leaf (-3)) (.leaf (0)))),
  (.branch 77 (.leaf (-2)) (.leaf (-1))),
  (.branch 67 (.branch 62 (.branch 59 (.branch 58 (.leaf (-21)) (.leaf (-20))) (.branch 60 (.leaf (-19)) (.branch 61 (.leaf (-18)) (.leaf (-17))))) (.branch 64 (.branch 63 (.leaf (-16)) (.leaf (-15))) (.branch 65 (.leaf (-14)) (.branch 66 (.leaf (-13)) (.leaf (-12)))))) (.branch 72 (.branch 69 (.branch 68 (.leaf (-11)) (.leaf (-10))) (.branch 70 (.leaf (-9)) (.branch 71 (.leaf (-8)) (.leaf (-7))))) (.branch 75 (.branch 73 (.leaf (-6)) (.branch 74 (.leaf (-5)) (.leaf (-4)))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 74 (.branch 72 (.branch 71 (.leaf (-8)) (.leaf (-7))) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_271_4160 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (7)) (.branch 13 (.leaf (0)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (5)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (8)) (.leaf (1))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (6)) (.leaf (0)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (5))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (7)) (.branch 38 (.leaf (4)) (.leaf (2)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (3)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 47 (.leaf (1)) (.leaf (0)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (3)) (.leaf (2))) (.branch 51 (.leaf (8)) (.branch 52 (.leaf (0)) (.leaf (1))))) (.branch 55 (.branch 54 (.leaf (4)) (.leaf (2))) (.branch 56 (.leaf (0)) (.branch 57 (.leaf (3)) (.leaf (1))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (2)) (.leaf (0))) (.branch 61 (.leaf (5)) (.branch 62 (.leaf (7)) (.leaf (1))))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (3))) (.branch 66 (.leaf (2)) (.branch 67 (.leaf (6)) (.leaf (0)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (1)) (.leaf (4))) (.branch 71 (.leaf (2)) (.branch 72 (.leaf (0)) (.leaf (3))))) (.branch 75 (.branch 74 (.leaf (1)) (.leaf (0))) (.branch 76 (.leaf (8)) (.branch 77 (.leaf (5)) (.leaf (2)))))))))
  code := certificateP9_4160
  counts := ![(.branch 36 (.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 33 (.leaf (8)) (.leaf (9)))))) (.branch 56 (.branch 44 (.branch 40 (.leaf (10)) (.leaf (11))) (.branch 48 (.leaf (12)) (.branch 52 (.leaf (13)) (.leaf (14))))) (.branch 68 (.branch 60 (.leaf (15)) (.branch 64 (.leaf (16)) (.leaf (17)))) (.branch 72 (.leaf (18)) (.branch 75 (.leaf (19)) (.leaf (20))))))),
  (.branch 35 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))) (.branch 58 (.branch 47 (.branch 41 (.leaf (7)) (.leaf (8))) (.branch 53 (.leaf (9)) (.leaf (10)))) (.branch 69 (.branch 63 (.leaf (11)) (.leaf (12))) (.branch 74 (.leaf (13)) (.leaf (14)))))),
  (.branch 39 (.branch 16 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))) (.branch 59 (.branch 50 (.branch 43 (.leaf (7)) (.leaf (8))) (.branch 55 (.leaf (9)) (.leaf (10)))) (.branch 71 (.branch 66 (.leaf (11)) (.leaf (12))) (.branch 78 (.leaf (13)) (.leaf (14)))))),
  (.branch 34 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 57 (.branch 42 (.leaf (5)) (.branch 49 (.leaf (6)) (.leaf (7)))) (.branch 65 (.leaf (8)) (.branch 73 (.leaf (9)) (.leaf (10)))))),
  (.branch 38 (.branch 6 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 54 (.leaf (3)) (.branch 70 (.leaf (4)) (.leaf (5))))),
  (.branch 45 (.branch 15 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))) (.branch 61 (.leaf (3)) (.branch 77 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 67 (.leaf (3)) (.leaf (4))))),
  (.branch 37 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3)))),
  (.branch 51 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 76 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 36 (.leaf (-29)) (.leaf (-30)))),
  (.branch 35 (.branch 2 (.leaf (0)) (.branch 24 (.leaf (-11)) (.leaf (-13)))) (.branch 63 (.leaf (-14)) (.branch 74 (.leaf (-15)) (.leaf (-16))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 43 (.leaf (-4)) (.branch 59 (.leaf (-5)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-24)) (.leaf (-28)))),
  (.branch 6 (.leaf (0)) (.leaf (-39))),
  (.branch 15 (.leaf (0)) (.branch 45 (.leaf (-3)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.branch 46 (.leaf (-13)) (.leaf (-14)))),
  (.branch 37 (.branch 12 (.leaf (0)) (.leaf (-15))) (.branch 62 (.leaf (-17)) (.leaf (-19)))),
  (.branch 23 (.leaf (0)) (.branch 76 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 76 (.leaf (-30)) (.branch 77 (.leaf (-20)) (.leaf (-10)))),
  (.branch 76 (.branch 75 (.leaf (-16)) (.leaf (-13))) (.branch 77 (.leaf (-10)) (.leaf (-7)))),
  (.branch 74 (.branch 72 (.leaf (-7)) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.branch 74 (.branch 58 (.branch 50 (.leaf (-28)) (.leaf (-27))) (.branch 66 (.leaf (-26)) (.leaf (-25)))) (.branch 76 (.branch 75 (.leaf (-20)) (.leaf (-15))) (.branch 77 (.leaf (-10)) (.leaf (-5))))),
  (.branch 72 (.branch 39 (.branch 7 (.leaf (-39)) (.branch 23 (.leaf (-38)) (.leaf (-37)))) (.branch 55 (.leaf (-36)) (.branch 71 (.leaf (-35)) (.leaf (-31))))) (.branch 75 (.branch 73 (.leaf (-27)) (.branch 74 (.leaf (-23)) (.leaf (-19)))) (.branch 76 (.leaf (-15)) (.branch 77 (.leaf (-11)) (.leaf (-7)))))),
  (.branch 46 (.leaf (-9)) (.branch 62 (.leaf (-8)) (.leaf (-7)))),
  (.branch 72 (.branch 69 (.branch 47 (.leaf (-14)) (.branch 68 (.leaf (-13)) (.leaf (-12)))) (.branch 70 (.leaf (-11)) (.branch 71 (.leaf (-10)) (.leaf (-9))))) (.branch 75 (.branch 73 (.leaf (-8)) (.branch 74 (.leaf (-7)) (.leaf (-6)))) (.branch 76 (.leaf (-5)) (.branch 77 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 70 (.branch 66 (.branch 64 (.branch 63 (.leaf (-19)) (.leaf (-18))) (.branch 65 (.leaf (-17)) (.leaf (-16)))) (.branch 68 (.branch 67 (.leaf (-15)) (.leaf (-14))) (.branch 69 (.leaf (-13)) (.leaf (-12))))) (.branch 74 (.branch 72 (.branch 71 (.leaf (-11)) (.leaf (-10))) (.branch 73 (.leaf (-9)) (.leaf (-8)))) (.branch 76 (.branch 75 (.leaf (-7)) (.leaf (-6))) (.branch 77 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 77 (.leaf (-5)) (.leaf (-4)))]
def witnessP9_271_4161 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (7)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (0)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (6)) (.leaf (1))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (8)) (.leaf (0)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (4))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (5)) (.branch 38 (.leaf (4)) (.leaf (2)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (3)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (4))) (.branch 46 (.leaf (7)) (.branch 47 (.leaf (1)) (.leaf (0)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (3)) (.leaf (2))) (.branch 51 (.leaf (6)) (.branch 52 (.leaf (0)) (.leaf (1))))) (.branch 55 (.branch 54 (.leaf (4)) (.leaf (2))) (.branch 56 (.leaf (0)) (.branch 57 (.leaf (3)) (.leaf (1))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (2)) (.leaf (0))) (.branch 61 (.leaf (4)) (.branch 62 (.leaf (5)) (.leaf (1))))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (3))) (.branch 66 (.leaf (2)) (.branch 67 (.leaf (8)) (.leaf (0)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (1)) (.leaf (4))) (.branch 71 (.leaf (2)) (.branch 72 (.leaf (0)) (.leaf (3))))) (.branch 75 (.branch 74 (.leaf (1)) (.leaf (0))) (.branch 76 (.leaf (6)) (.branch 77 (.leaf (4)) (.leaf (2)))))))))
  code := certificateP9_4161
  counts := ![(.branch 36 (.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 33 (.leaf (8)) (.leaf (9)))))) (.branch 56 (.branch 44 (.branch 40 (.leaf (10)) (.leaf (11))) (.branch 48 (.leaf (12)) (.branch 52 (.leaf (13)) (.leaf (14))))) (.branch 68 (.branch 60 (.leaf (15)) (.branch 64 (.leaf (16)) (.leaf (17)))) (.branch 72 (.leaf (18)) (.branch 75 (.leaf (19)) (.leaf (20))))))),
  (.branch 35 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))) (.branch 58 (.branch 47 (.branch 41 (.leaf (7)) (.leaf (8))) (.branch 53 (.leaf (9)) (.leaf (10)))) (.branch 69 (.branch 63 (.leaf (11)) (.leaf (12))) (.branch 74 (.leaf (13)) (.leaf (14)))))),
  (.branch 39 (.branch 16 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))) (.branch 59 (.branch 50 (.branch 43 (.leaf (7)) (.leaf (8))) (.branch 55 (.leaf (9)) (.leaf (10)))) (.branch 71 (.branch 66 (.leaf (11)) (.leaf (12))) (.branch 78 (.leaf (13)) (.leaf (14)))))),
  (.branch 34 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 57 (.branch 42 (.leaf (5)) (.branch 49 (.leaf (6)) (.leaf (7)))) (.branch 65 (.leaf (8)) (.branch 73 (.leaf (9)) (.leaf (10)))))),
  (.branch 38 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))) (.branch 61 (.branch 45 (.leaf (5)) (.branch 54 (.leaf (6)) (.leaf (7)))) (.branch 70 (.leaf (8)) (.branch 77 (.leaf (9)) (.leaf (10)))))),
  (.branch 37 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3)))),
  (.branch 51 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 76 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 67 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 36 (.leaf (-29)) (.leaf (-30)))),
  (.branch 35 (.branch 2 (.leaf (0)) (.branch 24 (.leaf (-11)) (.leaf (-13)))) (.branch 63 (.leaf (-14)) (.branch 74 (.leaf (-15)) (.leaf (-16))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 43 (.leaf (-4)) (.branch 59 (.leaf (-5)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-24)) (.leaf (-28)))),
  (.branch 6 (.leaf (0)) (.branch 45 (.leaf (-2)) (.leaf (-3)))),
  (.branch 37 (.branch 12 (.leaf (0)) (.leaf (-15))) (.branch 62 (.leaf (-17)) (.leaf (-19)))),
  (.branch 23 (.leaf (0)) (.branch 76 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-32))),
  (.branch 28 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 76 (.leaf (-30)) (.branch 77 (.leaf (-20)) (.leaf (-10)))),
  (.branch 76 (.branch 75 (.leaf (-16)) (.leaf (-13))) (.branch 77 (.leaf (-10)) (.leaf (-7)))),
  (.branch 74 (.branch 72 (.leaf (-7)) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.branch 74 (.branch 58 (.branch 50 (.leaf (-28)) (.leaf (-27))) (.branch 66 (.leaf (-26)) (.leaf (-25)))) (.branch 76 (.branch 75 (.leaf (-20)) (.leaf (-15))) (.branch 77 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-3)),
  (.branch 70 (.branch 66 (.branch 64 (.branch 63 (.leaf (-19)) (.leaf (-18))) (.branch 65 (.leaf (-17)) (.leaf (-16)))) (.branch 68 (.branch 67 (.leaf (-15)) (.leaf (-14))) (.branch 69 (.leaf (-13)) (.leaf (-12))))) (.branch 74 (.branch 72 (.branch 71 (.leaf (-11)) (.leaf (-10))) (.branch 73 (.leaf (-9)) (.leaf (-8)))) (.branch 76 (.branch 75 (.leaf (-7)) (.leaf (-6))) (.branch 77 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 77 (.leaf (-5)) (.leaf (-4))),
  (.branch 62 (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (-32)) (.leaf (-31))) (.branch 49 (.leaf (-30)) (.leaf (-29)))) (.branch 52 (.branch 51 (.leaf (-28)) (.leaf (-27))) (.branch 53 (.leaf (-26)) (.leaf (-25))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (-24)) (.leaf (-23))) (.branch 57 (.leaf (-22)) (.leaf (-21)))) (.branch 60 (.branch 59 (.leaf (-20)) (.leaf (-19))) (.branch 61 (.leaf (-18)) (.leaf (-17)))))) (.branch 70 (.branch 66 (.branch 64 (.branch 63 (.leaf (-16)) (.leaf (-15))) (.branch 65 (.leaf (-14)) (.leaf (-13)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-11))) (.branch 69 (.leaf (-10)) (.leaf (-9))))) (.branch 74 (.branch 72 (.branch 71 (.leaf (-8)) (.leaf (-7))) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 72 (.branch 69 (.branch 68 (.leaf (-11)) (.leaf (-10))) (.branch 70 (.leaf (-9)) (.branch 71 (.leaf (-8)) (.leaf (-7))))) (.branch 75 (.branch 73 (.leaf (-6)) (.branch 74 (.leaf (-5)) (.leaf (-4)))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_271_4162 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (7)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (3))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (6))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (4)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (8)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (0)) (.leaf (3)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (2)) (.leaf (0))))) (.branch 36 (.branch 35 (.leaf (4)) (.leaf (1))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (7)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (3)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (6))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (2)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (4)) (.leaf (0))) (.branch 51 (.leaf (1)) (.branch 52 (.leaf (8)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (3))) (.branch 56 (.leaf (1)) (.branch 57 (.leaf (0)) (.leaf (5))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (0)) (.leaf (2))) (.branch 61 (.leaf (1)) (.branch 62 (.leaf (4)) (.leaf (0))))) (.branch 65 (.branch 64 (.leaf (7)) (.leaf (1))) (.branch 66 (.leaf (2)) (.branch 67 (.leaf (0)) (.leaf (3)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (0)) (.leaf (1))) (.branch 71 (.leaf (6)) (.branch 72 (.leaf (2)) (.leaf (0))))) (.branch 75 (.branch 74 (.leaf (4)) (.leaf (1))) (.branch 76 (.leaf (0)) (.branch 77 (.leaf (2)) (.leaf (8)))))))))
  code := certificateP9_4162
  counts := ![(.branch 37 (.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 30 (.leaf (9)) (.branch 34 (.leaf (10)) (.leaf (11)))))) (.branch 57 (.branch 47 (.branch 40 (.leaf (12)) (.branch 44 (.leaf (13)) (.leaf (14)))) (.branch 50 (.leaf (15)) (.branch 53 (.leaf (16)) (.leaf (17))))) (.branch 67 (.branch 59 (.leaf (18)) (.branch 63 (.leaf (19)) (.leaf (20)))) (.branch 73 (.branch 69 (.leaf (21)) (.leaf (22))) (.branch 76 (.leaf (23)) (.leaf (24))))))),
  (.branch 36 (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))) (.branch 56 (.branch 46 (.branch 41 (.leaf (8)) (.leaf (9))) (.branch 51 (.leaf (10)) (.leaf (11)))) (.branch 65 (.branch 61 (.leaf (12)) (.leaf (13))) (.branch 70 (.leaf (14)) (.branch 75 (.leaf (15)) (.leaf (16))))))),
  (.branch 38 (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))) (.branch 60 (.branch 48 (.branch 43 (.leaf (7)) (.leaf (8))) (.branch 54 (.leaf (9)) (.leaf (10)))) (.branch 72 (.branch 66 (.leaf (11)) (.leaf (12))) (.branch 77 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 62 (.branch 49 (.leaf (3)) (.leaf (4))) (.branch 74 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 45 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 71 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3)))),
  (.branch 52 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 78 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 30 (.branch 11 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 14 (.leaf (-6)) (.branch 20 (.leaf (-7)) (.leaf (-9))))) (.branch 53 (.branch 40 (.leaf (-10)) (.branch 50 (.leaf (-11)) (.leaf (-12)))) (.branch 59 (.leaf (-13)) (.branch 69 (.leaf (-15)) (.leaf (-16)))))),
  (.branch 2 (.leaf (0)) (.branch 26 (.leaf (-23)) (.leaf (-26)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 43 (.leaf (-10)) (.branch 48 (.leaf (-12)) (.leaf (-15))))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 10 (.leaf (0)) (.branch 35 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.branch 64 (.leaf (-13)) (.leaf (-14)))),
  (.branch 25 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 77 (.leaf (-16)) (.leaf (-14))),
  (.branch 71 (.branch 66 (.leaf (-26)) (.leaf (-25))) (.branch 76 (.leaf (-24)) (.branch 77 (.leaf (-16)) (.leaf (-8))))),
  (.branch 49 (.leaf (-15)) (.leaf (-14))),
  (.branch 73 (.branch 70 (.branch 69 (.leaf (-10)) (.leaf (-9))) (.branch 71 (.leaf (-8)) (.branch 72 (.leaf (-7)) (.leaf (-6))))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1)))),
  (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (-20)) (.leaf (-19))) (.branch 61 (.leaf (-18)) (.branch 62 (.leaf (-17)) (.leaf (-16))))) (.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-14))) (.branch 66 (.leaf (-13)) (.branch 67 (.leaf (-12)) (.leaf (-11)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (-10)) (.leaf (-9))) (.branch 71 (.leaf (-8)) (.branch 72 (.leaf (-7)) (.leaf (-6))))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 74 (.branch 72 (.leaf (-7)) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.branch 71 (.branch 67 (.branch 65 (.leaf (-14)) (.branch 66 (.leaf (-13)) (.leaf (-12)))) (.branch 69 (.branch 68 (.leaf (-11)) (.leaf (-10))) (.branch 70 (.leaf (-9)) (.leaf (-8))))) (.branch 74 (.branch 72 (.leaf (-7)) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.leaf (-1)) (.leaf (0)))]
def witnessP9_271_4163 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (6))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (7)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (5))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (4)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (3))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (0)) (.leaf (6)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (2))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (5)) (.branch 38 (.leaf (2)) (.leaf (8)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (3)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (6))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (4)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (3)) (.leaf (2))) (.branch 51 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (5))))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (0))) (.branch 56 (.leaf (3)) (.branch 57 (.leaf (7)) (.leaf (1))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (0)) (.leaf (6))) (.branch 61 (.leaf (2)) (.branch 62 (.leaf (4)) (.leaf (0))))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (3))) (.branch 66 (.leaf (2)) (.branch 67 (.leaf (0)) (.leaf (5)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (1)) (.leaf (2))) (.branch 71 (.leaf (0)) (.branch 72 (.leaf (3)) (.leaf (4))))) (.branch 75 (.branch 74 (.leaf (1)) (.leaf (0))) (.branch 76 (.leaf (6)) (.branch 77 (.leaf (2)) (.leaf (8)))))))))
  code := certificateP9_4163
  counts := ![(.branch 36 (.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 28 (.leaf (7)) (.branch 32 (.leaf (8)) (.leaf (9)))))) (.branch 55 (.branch 44 (.branch 40 (.leaf (10)) (.leaf (11))) (.branch 47 (.leaf (12)) (.branch 51 (.leaf (13)) (.leaf (14))))) (.branch 67 (.branch 59 (.leaf (15)) (.branch 63 (.leaf (16)) (.leaf (17)))) (.branch 71 (.leaf (18)) (.branch 75 (.leaf (19)) (.leaf (20))))))),
  (.branch 35 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))) (.branch 58 (.branch 46 (.branch 41 (.leaf (7)) (.leaf (8))) (.branch 52 (.leaf (9)) (.leaf (10)))) (.branch 69 (.branch 64 (.leaf (11)) (.leaf (12))) (.branch 74 (.leaf (13)) (.leaf (14)))))),
  (.branch 38 (.branch 15 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))) (.branch 61 (.branch 50 (.branch 43 (.leaf (7)) (.leaf (8))) (.branch 54 (.leaf (9)) (.leaf (10)))) (.branch 70 (.branch 66 (.leaf (11)) (.leaf (12))) (.branch 77 (.leaf (13)) (.leaf (14)))))),
  (.branch 33 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 56 (.branch 42 (.leaf (5)) (.branch 49 (.leaf (6)) (.leaf (7)))) (.branch 65 (.leaf (8)) (.branch 72 (.leaf (9)) (.leaf (10)))))),
  (.branch 34 (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 62 (.branch 48 (.leaf (3)) (.leaf (4))) (.branch 73 (.leaf (5)) (.leaf (6))))),
  (.branch 37 (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.leaf (3)) (.branch 68 (.leaf (4)) (.leaf (5))))),
  (.branch 45 (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 60 (.leaf (3)) (.branch 76 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.leaf (0)) (.branch 57 (.leaf (1)) (.leaf (2)))),
  (.branch 39 (.leaf (0)) (.branch 78 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-29)) (.leaf (-37)))),
  (.branch 35 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))) (.branch 46 (.leaf (-14)) (.branch 74 (.leaf (-15)) (.leaf (-16))))),
  (.branch 31 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))) (.branch 54 (.leaf (-5)) (.branch 70 (.leaf (-6)) (.leaf (-8))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 17 (.leaf (-6)) (.branch 56 (.leaf (-7)) (.leaf (-8))))),
  (.branch 34 (.branch 9 (.leaf (0)) (.leaf (-9))) (.branch 73 (.leaf (-13)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (-48)) (.leaf (-51)))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (-8))) (.branch 60 (.leaf (-11)) (.leaf (-12)))),
  (.branch 18 (.leaf (0)) (.leaf (-21))),
  (.leaf (0))]
  high := ![(.branch 64 (.branch 52 (.branch 48 (.leaf (-37)) (.leaf (-36))) (.branch 56 (.leaf (-35)) (.branch 60 (.leaf (-34)) (.leaf (-33))))) (.branch 72 (.branch 68 (.leaf (-32)) (.leaf (-31))) (.branch 76 (.leaf (-30)) (.branch 77 (.leaf (-20)) (.leaf (-10)))))),
  (.branch 76 (.branch 75 (.leaf (-16)) (.leaf (-13))) (.branch 77 (.leaf (-10)) (.leaf (-7)))),
  (.branch 71 (.leaf (-8)) (.leaf (-7))),
  (.branch 75 (.branch 73 (.leaf (-8)) (.branch 74 (.leaf (-7)) (.leaf (-6)))) (.branch 76 (.leaf (-5)) (.branch 77 (.leaf (-4)) (.leaf (-3))))),
  (.branch 75 (.branch 74 (.leaf (-16)) (.leaf (-14))) (.branch 76 (.leaf (-12)) (.branch 77 (.leaf (-10)) (.leaf (-8))))),
  (.branch 72 (.branch 69 (.branch 22 (.leaf (-51)) (.leaf (-50))) (.branch 70 (.leaf (-45)) (.branch 71 (.leaf (-40)) (.leaf (-35))))) (.branch 75 (.branch 73 (.leaf (-30)) (.branch 74 (.leaf (-25)) (.leaf (-20)))) (.branch 76 (.leaf (-15)) (.branch 77 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 61 (.leaf (-12)) (.branch 77 (.leaf (-10)) (.leaf (-5)))),
  (.branch 67 (.branch 62 (.branch 59 (.branch 58 (.leaf (-21)) (.leaf (-20))) (.branch 60 (.leaf (-19)) (.branch 61 (.leaf (-18)) (.leaf (-17))))) (.branch 64 (.branch 63 (.leaf (-16)) (.leaf (-15))) (.branch 65 (.leaf (-14)) (.branch 66 (.leaf (-13)) (.leaf (-12)))))) (.branch 72 (.branch 69 (.branch 68 (.leaf (-11)) (.leaf (-10))) (.branch 70 (.leaf (-9)) (.branch 71 (.leaf (-8)) (.leaf (-7))))) (.branch 75 (.branch 73 (.leaf (-6)) (.branch 74 (.leaf (-5)) (.leaf (-4)))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_271_4164 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (5)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (3))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (7))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (4))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (8)) (.branch 33 (.leaf (1)) (.leaf (0))))) (.branch 36 (.branch 35 (.leaf (3)) (.leaf (2))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (5)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (2))) (.branch 42 (.leaf (3)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (6))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (3)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (2)) (.branch 52 (.leaf (4)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (3))) (.branch 56 (.leaf (2)) (.branch 57 (.leaf (0)) (.leaf (7))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (1)) (.leaf (0))) (.branch 61 (.leaf (3)) (.branch 62 (.leaf (2)) (.leaf (0))))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (5))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (2)) (.leaf (3)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (1)) (.leaf (0))) (.branch 71 (.leaf (8)) (.branch 72 (.leaf (2)) (.leaf (0))))) (.branch 75 (.branch 74 (.leaf (3)) (.leaf (1))) (.branch 76 (.leaf (0)) (.branch 77 (.leaf (2)) (.leaf (4)))))))))
  code := certificateP9_4164
  counts := ![(.branch 37 (.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 31 (.leaf (9)) (.branch 34 (.leaf (10)) (.leaf (11)))))) (.branch 57 (.branch 47 (.branch 40 (.leaf (12)) (.branch 44 (.leaf (13)) (.leaf (14)))) (.branch 50 (.leaf (15)) (.branch 53 (.leaf (16)) (.leaf (17))))) (.branch 66 (.branch 60 (.leaf (18)) (.branch 63 (.leaf (19)) (.leaf (20)))) (.branch 73 (.branch 70 (.leaf (21)) (.leaf (22))) (.branch 76 (.leaf (23)) (.leaf (24))))))),
  (.branch 38 (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))) (.branch 59 (.branch 49 (.branch 43 (.leaf (8)) (.leaf (9))) (.branch 54 (.leaf (10)) (.leaf (11)))) (.branch 69 (.branch 64 (.leaf (12)) (.leaf (13))) (.branch 75 (.leaf (14)) (.leaf (15)))))),
  (.branch 41 (.branch 20 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))) (.branch 62 (.branch 51 (.branch 46 (.leaf (8)) (.leaf (9))) (.branch 56 (.leaf (10)) (.leaf (11)))) (.branch 72 (.branch 67 (.leaf (12)) (.leaf (13))) (.branch 77 (.leaf (14)) (.leaf (15)))))),
  (.branch 35 (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))) (.branch 55 (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))) (.branch 68 (.branch 61 (.leaf (9)) (.leaf (10))) (.branch 74 (.leaf (11)) (.leaf (12)))))),
  (.branch 52 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 78 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 58 (.leaf (1)) (.leaf (2)))),
  (.branch 32 (.leaf (0)) (.branch 71 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-16))) (.branch 12 (.leaf (-17)) (.branch 17 (.leaf (-18)) (.leaf (-19))))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.branch 6 (.leaf (0)) (.leaf (-33))),
  (.branch 19 (.leaf (0)) (.leaf (-20))),
  (.branch 32 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 67 (.leaf (-9)) (.branch 77 (.leaf (-8)) (.leaf (-4)))),
  (.branch 76 (.branch 70 (.leaf (-19)) (.leaf (-15))) (.branch 77 (.leaf (-10)) (.leaf (-5)))),
  (.branch 57 (.leaf (-6)) (.leaf (-5))),
  (.branch 76 (.branch 75 (.leaf (-8)) (.leaf (-6))) (.branch 77 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 71 (.branch 68 (.branch 66 (.leaf (-13)) (.branch 67 (.leaf (-12)) (.leaf (-11)))) (.branch 69 (.leaf (-10)) (.branch 70 (.leaf (-9)) (.leaf (-8))))) (.branch 74 (.branch 72 (.leaf (-7)) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 61 (.branch 53 (.branch 49 (.branch 47 (.branch 46 (.leaf (-33)) (.leaf (-32))) (.branch 48 (.leaf (-31)) (.leaf (-30)))) (.branch 51 (.branch 50 (.leaf (-29)) (.leaf (-28))) (.branch 52 (.leaf (-27)) (.leaf (-26))))) (.branch 57 (.branch 55 (.branch 54 (.leaf (-25)) (.leaf (-24))) (.branch 56 (.leaf (-23)) (.leaf (-22)))) (.branch 59 (.branch 58 (.leaf (-21)) (.leaf (-20))) (.branch 60 (.leaf (-19)) (.leaf (-18)))))) (.branch 69 (.branch 65 (.branch 63 (.branch 62 (.leaf (-17)) (.leaf (-16))) (.branch 64 (.leaf (-15)) (.leaf (-14)))) (.branch 67 (.branch 66 (.leaf (-13)) (.leaf (-12))) (.branch 68 (.leaf (-11)) (.leaf (-10))))) (.branch 73 (.branch 71 (.branch 70 (.leaf (-9)) (.leaf (-8))) (.branch 72 (.leaf (-7)) (.leaf (-6)))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (-20)) (.leaf (-19))) (.branch 61 (.leaf (-18)) (.branch 62 (.leaf (-17)) (.leaf (-16))))) (.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-14))) (.branch 66 (.leaf (-13)) (.branch 67 (.leaf (-12)) (.leaf (-11)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (-10)) (.leaf (-9))) (.branch 71 (.leaf (-8)) (.branch 72 (.leaf (-7)) (.leaf (-6))))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 74 (.branch 72 (.leaf (-7)) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_271_4165 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (7)) (.branch 8 (.leaf (5)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (4)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (6))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (8)) (.leaf (4))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (5))))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (3))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (4)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (6))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (7)) (.leaf (3))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (4)) (.branch 38 (.leaf (2)) (.leaf (5)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (3)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (4)) (.leaf (0))) (.branch 46 (.leaf (8)) (.branch 47 (.leaf (6)) (.leaf (1)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (2)) (.branch 52 (.leaf (4)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (5))) (.branch 56 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (0))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (7)) (.leaf (4))) (.branch 61 (.leaf (1)) (.branch 62 (.leaf (0)) (.leaf (6))))) (.branch 65 (.branch 64 (.leaf (2)) (.leaf (3))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (1)) (.leaf (4)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (2)) (.leaf (5))) (.branch 71 (.leaf (0)) (.branch 72 (.leaf (8)) (.leaf (3))))) (.branch 75 (.branch 74 (.leaf (1)) (.leaf (0))) (.branch 76 (.leaf (4)) (.branch 77 (.leaf (2)) (.leaf (6)))))))))
  code := certificateP9_4165
  counts := ![(.branch 36 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))) (.branch 58 (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.branch 53 (.leaf (12)) (.leaf (13))))) (.branch 66 (.branch 62 (.leaf (14)) (.leaf (15))) (.branch 71 (.leaf (16)) (.branch 75 (.leaf (17)) (.leaf (18))))))),
  (.branch 35 (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 54 (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))) (.branch 67 (.branch 61 (.leaf (9)) (.leaf (10))) (.branch 74 (.leaf (11)) (.leaf (12)))))),
  (.branch 38 (.branch 17 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))) (.branch 56 (.branch 43 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))) (.branch 69 (.branch 64 (.leaf (9)) (.leaf (10))) (.branch 77 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 57 (.branch 42 (.leaf (5)) (.branch 50 (.leaf (6)) (.leaf (7)))) (.branch 65 (.leaf (8)) (.branch 73 (.leaf (9)) (.leaf (10)))))),
  (.branch 37 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 60 (.branch 44 (.leaf (5)) (.branch 52 (.leaf (6)) (.leaf (7)))) (.branch 68 (.leaf (8)) (.branch 76 (.leaf (9)) (.leaf (10)))))),
  (.branch 39 (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 55 (.leaf (3)) (.branch 70 (.leaf (4)) (.leaf (5))))),
  (.branch 47 (.branch 16 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))) (.branch 63 (.leaf (3)) (.branch 78 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 46 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 72 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-10))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 30 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-3)) (.leaf (-4)))) (.branch 56 (.branch 43 (.leaf (-5)) (.leaf (-6))) (.branch 69 (.leaf (-7)) (.leaf (-8))))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-24)) (.leaf (-27)))),
  (.branch 5 (.leaf (0)) (.leaf (-14))),
  (.branch 39 (.branch 8 (.leaf (0)) (.leaf (-38))) (.branch 70 (.leaf (-39)) (.leaf (-40)))),
  (.branch 31 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 76 (.branch 67 (.leaf (-10)) (.leaf (-9))) (.branch 77 (.leaf (-6)) (.leaf (-3)))),
  (.branch 75 (.branch 68 (.leaf (-9)) (.leaf (-8))) (.branch 76 (.leaf (-6)) (.branch 77 (.leaf (-4)) (.leaf (-2))))),
  (.branch 70 (.leaf (-8)) (.leaf (-7))),
  (.branch 74 (.branch 58 (.leaf (-27)) (.branch 66 (.leaf (-26)) (.leaf (-25)))) (.branch 76 (.branch 75 (.leaf (-20)) (.leaf (-15))) (.branch 77 (.leaf (-10)) (.leaf (-5))))),
  (.branch 61 (.branch 45 (.leaf (-14)) (.branch 53 (.leaf (-13)) (.leaf (-12)))) (.branch 69 (.leaf (-11)) (.branch 77 (.leaf (-10)) (.leaf (-5))))),
  (.branch 74 (.branch 72 (.branch 71 (.leaf (-40)) (.leaf (-35))) (.branch 73 (.leaf (-30)) (.leaf (-25)))) (.branch 76 (.branch 75 (.leaf (-20)) (.leaf (-15))) (.branch 77 (.leaf (-10)) (.leaf (-5))))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 68 (.branch 63 (.branch 61 (.branch 60 (.leaf (-19)) (.leaf (-18))) (.branch 62 (.leaf (-17)) (.leaf (-16)))) (.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-14))) (.branch 66 (.leaf (-13)) (.branch 67 (.leaf (-12)) (.leaf (-11)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (-10)) (.leaf (-9))) (.branch 71 (.leaf (-8)) (.branch 72 (.leaf (-7)) (.leaf (-6))))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 75 (.branch 73 (.leaf (-6)) (.branch 74 (.leaf (-5)) (.leaf (-4)))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_271_4166 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (8)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (6)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (7))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (8))))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (3))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (6)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (7))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (4)) (.leaf (3))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (5)) (.branch 38 (.leaf (2)) (.leaf (8)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (3)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (6)) (.leaf (0))) (.branch 46 (.leaf (4)) (.branch 47 (.leaf (7)) (.leaf (1)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (2)) (.branch 52 (.leaf (5)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (8))) (.branch 56 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (0))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (4)) (.leaf (6))) (.branch 61 (.leaf (1)) (.branch 62 (.leaf (0)) (.leaf (7))))) (.branch 65 (.branch 64 (.leaf (2)) (.leaf (3))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (1)) (.leaf (5)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (2)) (.leaf (8))) (.branch 71 (.leaf (0)) (.branch 72 (.leaf (4)) (.leaf (3))))) (.branch 75 (.branch 74 (.leaf (1)) (.leaf (0))) (.branch 76 (.leaf (6)) (.branch 77 (.leaf (2)) (.leaf (7)))))))))
  code := certificateP9_4166
  counts := ![(.branch 36 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))) (.branch 58 (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.branch 53 (.leaf (12)) (.leaf (13))))) (.branch 66 (.branch 62 (.leaf (14)) (.leaf (15))) (.branch 71 (.leaf (16)) (.branch 75 (.leaf (17)) (.leaf (18))))))),
  (.branch 35 (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 54 (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))) (.branch 67 (.branch 61 (.leaf (9)) (.leaf (10))) (.branch 74 (.leaf (11)) (.leaf (12)))))),
  (.branch 38 (.branch 17 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))) (.branch 56 (.branch 43 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))) (.branch 69 (.branch 64 (.leaf (9)) (.leaf (10))) (.branch 77 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 57 (.branch 42 (.leaf (5)) (.branch 50 (.leaf (6)) (.leaf (7)))) (.branch 65 (.leaf (8)) (.branch 73 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 59 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 72 (.leaf (5)) (.leaf (6))))),
  (.branch 37 (.branch 5 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 68 (.leaf (4)) (.leaf (5))))),
  (.branch 44 (.branch 13 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 60 (.leaf (3)) (.branch 76 (.leaf (4)) (.leaf (5))))),
  (.branch 47 (.branch 16 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))) (.branch 63 (.leaf (3)) (.branch 78 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 55 (.leaf (3)) (.branch 70 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-10))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 30 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-3)) (.leaf (-4)))) (.branch 56 (.branch 43 (.leaf (-5)) (.leaf (-6))) (.branch 69 (.leaf (-7)) (.leaf (-8))))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-24)) (.leaf (-27)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-53))),
  (.branch 13 (.leaf (0)) (.branch 44 (.leaf (-13)) (.leaf (-14)))),
  (.branch 31 (.leaf (0)) (.leaf (-1))),
  (.branch 39 (.branch 8 (.leaf (0)) (.leaf (-38))) (.branch 70 (.leaf (-39)) (.leaf (-40))))]
  high := ![(.branch 76 (.branch 67 (.leaf (-10)) (.leaf (-9))) (.branch 77 (.leaf (-6)) (.leaf (-3)))),
  (.branch 75 (.branch 68 (.leaf (-9)) (.leaf (-8))) (.branch 76 (.leaf (-6)) (.branch 77 (.leaf (-4)) (.leaf (-2))))),
  (.branch 70 (.leaf (-8)) (.leaf (-7))),
  (.branch 74 (.branch 58 (.leaf (-27)) (.branch 66 (.leaf (-26)) (.leaf (-25)))) (.branch 76 (.branch 75 (.leaf (-20)) (.leaf (-15))) (.branch 77 (.leaf (-10)) (.leaf (-5))))),
  (.branch 75 (.branch 73 (.leaf (-6)) (.branch 74 (.leaf (-5)) (.leaf (-4)))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.branch 72 (.branch 69 (.branch 6 (.leaf (-53)) (.branch 53 (.leaf (-52)) (.leaf (-50)))) (.branch 70 (.leaf (-45)) (.branch 71 (.leaf (-40)) (.leaf (-35))))) (.branch 75 (.branch 73 (.leaf (-30)) (.branch 74 (.leaf (-25)) (.leaf (-20)))) (.branch 76 (.leaf (-15)) (.branch 77 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 61 (.branch 45 (.leaf (-14)) (.leaf (-12))) (.branch 77 (.leaf (-10)) (.leaf (-5)))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 74 (.branch 72 (.branch 71 (.leaf (-40)) (.leaf (-35))) (.branch 73 (.leaf (-30)) (.leaf (-25)))) (.branch 76 (.branch 75 (.leaf (-20)) (.leaf (-15))) (.branch 77 (.leaf (-10)) (.leaf (-5)))))]
def witnessP9_271_4167 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (7)) (.branch 8 (.leaf (1)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (6))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (4)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (3))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (8)) (.leaf (2))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (6))))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (4))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (0)) (.leaf (3)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (5))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (7)) (.leaf (0))))) (.branch 36 (.branch 35 (.leaf (3)) (.leaf (1))) (.branch 37 (.leaf (6)) (.branch 38 (.leaf (2)) (.leaf (4)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (3)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (5)) (.leaf (0))) (.branch 46 (.leaf (8)) (.branch 47 (.leaf (1)) (.leaf (3)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (2)) (.leaf (6))) (.branch 51 (.leaf (0)) (.branch 52 (.leaf (4)) (.leaf (1))))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (3))) (.branch 56 (.leaf (0)) (.branch 57 (.leaf (5)) (.leaf (1))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (7)) (.leaf (2))) (.branch 61 (.leaf (3)) (.branch 62 (.leaf (0)) (.leaf (6))))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (4))) (.branch 66 (.leaf (2)) (.branch 67 (.leaf (0)) (.leaf (3)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (1)) (.leaf (5))) (.branch 71 (.leaf (2)) (.branch 72 (.leaf (8)) (.leaf (0))))) (.branch 75 (.branch 74 (.leaf (3)) (.leaf (1))) (.branch 76 (.leaf (6)) (.branch 77 (.leaf (2)) (.leaf (4)))))))))
  code := certificateP9_4167
  counts := ![(.branch 34 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))) (.branch 56 (.branch 45 (.branch 40 (.leaf (7)) (.leaf (8))) (.branch 51 (.leaf (9)) (.leaf (10)))) (.branch 67 (.branch 62 (.leaf (11)) (.leaf (12))) (.branch 73 (.leaf (13)) (.leaf (14)))))),
  (.branch 36 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))) (.branch 58 (.branch 47 (.branch 41 (.leaf (7)) (.leaf (8))) (.branch 53 (.leaf (9)) (.leaf (10)))) (.branch 69 (.branch 64 (.leaf (11)) (.leaf (12))) (.branch 75 (.leaf (13)) (.leaf (14)))))),
  (.branch 38 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))) (.branch 60 (.branch 49 (.branch 43 (.leaf (7)) (.leaf (8))) (.branch 54 (.leaf (9)) (.leaf (10)))) (.branch 71 (.branch 66 (.leaf (11)) (.leaf (12))) (.branch 77 (.leaf (13)) (.leaf (14)))))),
  (.branch 35 (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))) (.branch 55 (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))) (.branch 68 (.branch 61 (.leaf (9)) (.leaf (10))) (.branch 74 (.leaf (11)) (.leaf (12)))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 65 (.branch 52 (.leaf (3)) (.leaf (4))) (.branch 78 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 70 (.leaf (5)) (.leaf (6))))),
  (.branch 37 (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 63 (.branch 50 (.leaf (3)) (.leaf (4))) (.branch 76 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 46 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 72 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-32))) (.branch 17 (.leaf (-36)) (.branch 28 (.leaf (-37)) (.leaf (-38))))),
  (.branch 2 (.leaf (0)) (.leaf (-25))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 75 (.branch 68 (.leaf (-38)) (.branch 74 (.leaf (-35)) (.leaf (-28)))) (.branch 76 (.leaf (-21)) (.branch 77 (.leaf (-14)) (.leaf (-7))))),
  (.branch 70 (.branch 42 (.leaf (-25)) (.leaf (-24))) (.branch 76 (.leaf (-21)) (.branch 77 (.leaf (-14)) (.leaf (-7))))),
  (.branch 55 (.leaf (-12)) (.branch 72 (.leaf (-10)) (.leaf (-7)))),
  (.branch 76 (.branch 75 (.leaf (-8)) (.leaf (-6))) (.branch 77 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 74 (.branch 72 (.branch 71 (.leaf (-8)) (.leaf (-7))) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.branch 77 (.leaf (-2)) (.leaf (-1))),
  (.branch 68 (.branch 63 (.branch 61 (.branch 60 (.leaf (-19)) (.leaf (-18))) (.branch 62 (.leaf (-17)) (.leaf (-16)))) (.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-14))) (.branch 66 (.leaf (-13)) (.branch 67 (.leaf (-12)) (.leaf (-11)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (-10)) (.leaf (-9))) (.branch 71 (.leaf (-8)) (.branch 72 (.leaf (-7)) (.leaf (-6))))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 75 (.branch 73 (.leaf (-6)) (.branch 74 (.leaf (-5)) (.leaf (-4)))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_271_4168 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (6)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (7)) (.branch 13 (.leaf (1)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (0))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (1)) (.leaf (3))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (6)) (.leaf (1))))) (.branch 26 (.branch 25 (.leaf (8)) (.leaf (0))) (.branch 27 (.leaf (3)) (.branch 28 (.leaf (2)) (.leaf (1)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (5))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (2)) (.leaf (3))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (2)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (3)) (.leaf (4)))) (.branch 45 (.branch 44 (.leaf (5)) (.leaf (0))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (1)) (.leaf (6)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (8)) (.branch 52 (.leaf (1)) (.leaf (2))))) (.branch 55 (.branch 54 (.leaf (4)) (.leaf (0))) (.branch 56 (.leaf (5)) (.branch 57 (.leaf (1)) (.leaf (3))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (0)) (.leaf (2))) (.branch 61 (.leaf (4)) (.branch 62 (.leaf (6)) (.leaf (1))))) (.branch 65 (.branch 64 (.leaf (7)) (.leaf (0))) (.branch 66 (.leaf (3)) (.branch 67 (.leaf (2)) (.leaf (1)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (0)) (.leaf (5))) (.branch 71 (.leaf (4)) (.branch 72 (.leaf (2)) (.leaf (3))))) (.branch 75 (.branch 74 (.leaf (1)) (.leaf (0))) (.branch 76 (.leaf (6)) (.branch 77 (.leaf (8)) (.leaf (2)))))))))
  code := certificateP9_4168
  counts := ![(.branch 36 (.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))) (.branch 55 (.branch 45 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 49 (.leaf (10)) (.leaf (11)))) (.branch 65 (.branch 59 (.leaf (12)) (.leaf (13))) (.branch 69 (.leaf (14)) (.branch 75 (.leaf (15)) (.leaf (16))))))),
  (.branch 35 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))) (.branch 57 (.branch 47 (.branch 41 (.leaf (7)) (.leaf (8))) (.branch 52 (.leaf (9)) (.leaf (10)))) (.branch 68 (.branch 63 (.leaf (11)) (.leaf (12))) (.branch 74 (.leaf (13)) (.leaf (14)))))),
  (.branch 39 (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))) (.branch 60 (.branch 46 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))) (.branch 72 (.branch 67 (.leaf (9)) (.leaf (10))) (.branch 78 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 58 (.branch 42 (.leaf (5)) (.branch 50 (.leaf (6)) (.leaf (7)))) (.branch 66 (.leaf (8)) (.branch 73 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.branch 71 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 70 (.leaf (5)) (.leaf (6))))),
  (.branch 37 (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 62 (.branch 48 (.leaf (3)) (.leaf (4))) (.branch 76 (.leaf (5)) (.leaf (6))))),
  (.branch 38 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3)))),
  (.branch 51 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 77 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 49 (.leaf (-5)) (.leaf (-6)))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))) (.branch 57 (.branch 29 (.leaf (-14)) (.leaf (-15))) (.branch 68 (.leaf (-16)) (.leaf (-17))))),
  (.branch 39 (.branch 33 (.leaf (0)) (.leaf (-3))) (.branch 72 (.leaf (-6)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 34 (.leaf (-24)) (.leaf (-25)))),
  (.branch 32 (.branch 4 (.leaf (0)) (.branch 22 (.leaf (-13)) (.leaf (-19)))) (.branch 61 (.leaf (-20)) (.branch 71 (.leaf (-25)) (.leaf (-26))))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-8)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.branch 48 (.leaf (-9)) (.leaf (-12)))),
  (.branch 12 (.leaf (0)) (.leaf (-14))),
  (.branch 25 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 76 (.branch 70 (.leaf (-6)) (.leaf (-5))) (.branch 77 (.leaf (-4)) (.leaf (-3)))),
  (.branch 75 (.branch 69 (.leaf (-17)) (.leaf (-16))) (.branch 76 (.leaf (-13)) (.branch 77 (.leaf (-10)) (.leaf (-7))))),
  (.branch 74 (.branch 73 (.leaf (-9)) (.leaf (-5))) (.branch 75 (.leaf (-1)) (.leaf (0)))),
  (.branch 75 (.branch 74 (.leaf (-25)) (.leaf (-20))) (.branch 76 (.leaf (-15)) (.branch 77 (.leaf (-10)) (.leaf (-5))))),
  (.branch 74 (.branch 72 (.leaf (-26)) (.branch 73 (.leaf (-24)) (.leaf (-22)))) (.branch 76 (.branch 75 (.leaf (-20)) (.leaf (-18))) (.branch 77 (.leaf (-16)) (.leaf (-14))))),
  (.branch 73 (.branch 71 (.branch 57 (.leaf (-9)) (.leaf (-8))) (.branch 72 (.leaf (-7)) (.leaf (-6)))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 77 (.leaf (-10)) (.leaf (-8)))),
  (.branch 71 (.branch 67 (.branch 65 (.leaf (-14)) (.branch 66 (.leaf (-13)) (.leaf (-12)))) (.branch 69 (.branch 68 (.leaf (-11)) (.leaf (-10))) (.branch 70 (.leaf (-9)) (.leaf (-8))))) (.branch 74 (.branch 72 (.leaf (-7)) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_271_4169 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (8)) (.branch 8 (.leaf (4)) (.leaf (6)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (7)) (.leaf (5))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (1)) (.leaf (6))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (8)) (.leaf (0))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (2)) (.leaf (5))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (7))) (.branch 27 (.leaf (4)) (.branch 28 (.leaf (1)) (.leaf (6)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (8)) (.leaf (5))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (4)) (.branch 38 (.leaf (6)) (.leaf (7)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (2))) (.branch 42 (.leaf (3)) (.leaf (5)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (0))) (.branch 46 (.leaf (8)) (.branch 47 (.leaf (4)) (.leaf (6)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (3)) (.branch 52 (.leaf (7)) (.leaf (5))))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (0))) (.branch 56 (.leaf (4)) (.branch 57 (.leaf (2)) (.leaf (6))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (8)) (.leaf (0))) (.branch 61 (.leaf (3)) (.branch 62 (.leaf (1)) (.leaf (5))))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (7))) (.branch 66 (.leaf (4)) (.branch 67 (.leaf (2)) (.leaf (6)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (0)) (.leaf (1))) (.branch 71 (.leaf (3)) (.branch 72 (.leaf (8)) (.leaf (5))))) (.branch 75 (.branch 74 (.leaf (0)) (.leaf (2))) (.branch 76 (.leaf (4)) (.branch 77 (.leaf (6)) (.leaf (7)))))))))
  code := certificateP9_4169
  counts := ![(.branch 35 (.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))) (.branch 55 (.branch 45 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 50 (.leaf (10)) (.leaf (11)))) (.branch 64 (.branch 60 (.leaf (12)) (.leaf (13))) (.branch 69 (.leaf (14)) (.branch 74 (.leaf (15)) (.leaf (16))))))),
  (.branch 36 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 44 (.leaf (5)) (.leaf (6))) (.branch 62 (.leaf (7)) (.branch 70 (.leaf (8)) (.leaf (9)))))),
  (.branch 41 (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))) (.branch 57 (.branch 49 (.leaf (5)) (.leaf (6))) (.branch 67 (.leaf (7)) (.branch 75 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.branch 71 (.leaf (7)) (.leaf (8)))))),
  (.branch 37 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 47 (.leaf (4)) (.leaf (5))) (.branch 66 (.leaf (6)) (.branch 76 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.branch 73 (.leaf (7)) (.leaf (8)))))),
  (.branch 38 (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 58 (.branch 48 (.leaf (4)) (.leaf (5))) (.branch 68 (.leaf (6)) (.branch 77 (.leaf (7)) (.leaf (8)))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 65 (.branch 52 (.leaf (3)) (.leaf (4))) (.branch 78 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 59 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 72 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 25 (.leaf (-31)) (.leaf (-34)))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-7)) (.leaf (-8)))) (.branch 44 (.leaf (-9)) (.branch 70 (.leaf (-10)) (.leaf (-11))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 57 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-27)) (.leaf (-30)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-7)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-23))),
  (.branch 9 (.leaf (0)) (.branch 38 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 75 (.branch 65 (.leaf (-34)) (.branch 70 (.leaf (-33)) (.leaf (-32)))) (.branch 76 (.leaf (-24)) (.branch 77 (.leaf (-16)) (.leaf (-8))))),
  (.branch 74 (.branch 72 (.branch 71 (.leaf (-11)) (.leaf (-10))) (.branch 73 (.leaf (-9)) (.leaf (-8)))) (.branch 76 (.branch 75 (.leaf (-7)) (.leaf (-6))) (.branch 77 (.leaf (-5)) (.leaf (-4))))),
  (.branch 76 (.leaf (-6)) (.branch 77 (.leaf (-5)) (.leaf (-4)))),
  (.branch 73 (.branch 62 (.branch 52 (.leaf (-30)) (.leaf (-29))) (.branch 72 (.leaf (-28)) (.leaf (-24)))) (.branch 75 (.branch 74 (.leaf (-20)) (.leaf (-16))) (.branch 76 (.leaf (-12)) (.branch 77 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 67 (.branch 57 (.leaf (-10)) (.leaf (-9))) (.branch 77 (.leaf (-8)) (.leaf (-4)))),
  (.branch 74 (.branch 54 (.branch 44 (.leaf (-23)) (.leaf (-22))) (.branch 64 (.leaf (-21)) (.leaf (-20)))) (.branch 76 (.branch 75 (.leaf (-16)) (.leaf (-12))) (.branch 77 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-4)),
  (.leaf (0)),
  (.branch 75 (.branch 73 (.leaf (-6)) (.branch 74 (.leaf (-5)) (.leaf (-4)))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_271_4170 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (8)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (6)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (7)) (.branch 18 (.leaf (4)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (8))) (.branch 22 (.leaf (5)) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (6))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (4)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (7)) (.leaf (0))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (5)) (.leaf (8))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (3))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (6)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (4)) (.leaf (2))) (.branch 42 (.leaf (0)) (.leaf (7)))) (.branch 45 (.branch 44 (.leaf (5)) (.leaf (1))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (8)) (.leaf (3)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (4)) (.branch 52 (.leaf (6)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (5))) (.branch 56 (.leaf (7)) (.branch 57 (.leaf (0)) (.leaf (2))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (3)) (.leaf (8))) (.branch 61 (.leaf (0)) (.branch 62 (.leaf (4)) (.leaf (1))))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (6))) (.branch 66 (.leaf (5)) (.branch 67 (.leaf (2)) (.leaf (0)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (7)) (.leaf (3))) (.branch 71 (.leaf (1)) (.branch 72 (.leaf (0)) (.leaf (8))))) (.branch 75 (.branch 74 (.leaf (4)) (.leaf (0))) (.branch 76 (.leaf (2)) (.branch 77 (.leaf (5)) (.leaf (6)))))))))
  code := certificateP9_4170
  counts := ![(.branch 38 (.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))) (.branch 57 (.branch 46 (.branch 42 (.leaf (11)) (.leaf (12))) (.branch 49 (.leaf (13)) (.branch 53 (.leaf (14)) (.leaf (15))))) (.branch 68 (.branch 61 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18)))) (.branch 72 (.leaf (19)) (.branch 75 (.leaf (20)) (.leaf (21))))))),
  (.branch 37 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 45 (.leaf (5)) (.leaf (6))) (.branch 63 (.leaf (7)) (.branch 71 (.leaf (8)) (.leaf (9)))))),
  (.branch 41 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))) (.branch 58 (.branch 50 (.leaf (5)) (.leaf (6))) (.branch 67 (.leaf (7)) (.branch 76 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 59 (.branch 48 (.leaf (4)) (.leaf (5))) (.branch 70 (.leaf (6)) (.leaf (7))))),
  (.branch 40 (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 62 (.branch 51 (.leaf (4)) (.leaf (5))) (.branch 74 (.leaf (6)) (.leaf (7))))),
  (.branch 44 (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))) (.branch 66 (.branch 55 (.leaf (4)) (.leaf (5))) (.branch 77 (.leaf (6)) (.leaf (7))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 65 (.branch 52 (.leaf (3)) (.leaf (4))) (.branch 78 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 69 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 60 (.branch 47 (.leaf (3)) (.leaf (4))) (.branch 73 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 23 (.leaf (-20)) (.leaf (-21)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-20)) (.leaf (-21)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-57))) (.branch 25 (.leaf (-58)) (.branch 36 (.leaf (-59)) (.leaf (-60))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (-29)) (.leaf (-30)))) (.branch 51 (.branch 40 (.leaf (-31)) (.leaf (-32))) (.branch 62 (.leaf (-33)) (.leaf (-34))))),
  (.branch 10 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 76 (.leaf (-21)) (.branch 77 (.leaf (-14)) (.leaf (-7)))),
  (.branch 74 (.branch 72 (.leaf (-21)) (.branch 73 (.leaf (-18)) (.leaf (-15)))) (.branch 76 (.branch 75 (.leaf (-12)) (.leaf (-9))) (.branch 77 (.leaf (-6)) (.leaf (-3))))),
  (.branch 68 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 77 (.leaf (-6)) (.leaf (-3)))),
  (.branch 73 (.branch 71 (.branch 37 (.leaf (-60)) (.leaf (-56))) (.branch 72 (.leaf (-49)) (.leaf (-42)))) (.branch 75 (.branch 74 (.leaf (-35)) (.leaf (-28))) (.branch 76 (.leaf (-21)) (.branch 77 (.leaf (-14)) (.leaf (-7)))))),
  (.branch 75 (.branch 63 (.leaf (-34)) (.leaf (-28))) (.branch 76 (.leaf (-21)) (.branch 77 (.leaf (-14)) (.leaf (-7))))),
  (.branch 11 (.leaf (-8)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 73 (.branch 71 (.branch 70 (.leaf (-9)) (.leaf (-8))) (.branch 72 (.leaf (-7)) (.leaf (-6)))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_271_4171 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (8))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (5))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (7))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (3)) (.leaf (0))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (4)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (8)) (.branch 28 (.leaf (1)) (.leaf (0)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (3))) (.branch 32 (.leaf (6)) (.branch 33 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (7)) (.leaf (4))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (5)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (3)) (.leaf (8)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (6))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (1)) (.leaf (0)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (4)) (.leaf (7))) (.branch 51 (.leaf (3)) (.branch 52 (.leaf (0)) (.leaf (5))))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (2))) (.branch 56 (.leaf (0)) (.branch 57 (.leaf (6)) (.leaf (8))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (3)) (.leaf (0))) (.branch 61 (.leaf (1)) (.branch 62 (.leaf (4)) (.leaf (2))))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (5))) (.branch 66 (.leaf (7)) (.branch 67 (.leaf (1)) (.leaf (0)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (2)) (.leaf (3))) (.branch 71 (.leaf (6)) (.branch 72 (.leaf (0)) (.leaf (1))))) (.branch 75 (.branch 74 (.leaf (8)) (.leaf (4))) (.branch 76 (.leaf (0)) (.branch 77 (.leaf (2)) (.leaf (5)))))))))
  code := certificateP9_4171
  counts := ![(.branch 37 (.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 33 (.leaf (8)) (.leaf (9)))))) (.branch 56 (.branch 44 (.branch 40 (.leaf (10)) (.leaf (11))) (.branch 48 (.leaf (12)) (.branch 52 (.leaf (13)) (.leaf (14))))) (.branch 68 (.branch 60 (.leaf (15)) (.branch 64 (.leaf (16)) (.leaf (17)))) (.branch 72 (.leaf (18)) (.branch 76 (.leaf (19)) (.leaf (20))))))),
  (.branch 34 (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 54 (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))) (.branch 67 (.branch 61 (.leaf (9)) (.leaf (10))) (.branch 73 (.leaf (11)) (.leaf (12)))))),
  (.branch 38 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))) (.branch 63 (.branch 46 (.leaf (5)) (.branch 55 (.leaf (6)) (.leaf (7)))) (.branch 69 (.leaf (8)) (.branch 77 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.branch 70 (.leaf (7)) (.leaf (8)))))),
  (.branch 36 (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 62 (.branch 49 (.leaf (3)) (.leaf (4))) (.branch 75 (.leaf (5)) (.leaf (6))))),
  (.branch 39 (.branch 14 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 65 (.branch 53 (.leaf (3)) (.leaf (4))) (.branch 78 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 71 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 4 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 66 (.leaf (4)) (.leaf (5))))),
  (.branch 43 (.branch 11 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 58 (.leaf (3)) (.branch 74 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-29))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 30 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 69 (.leaf (-2)) (.leaf (-3)))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-15)) (.leaf (-18)))) (.branch 51 (.leaf (-23)) (.branch 59 (.leaf (-24)) (.leaf (-29))))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-8)))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (-58))) (.branch 50 (.leaf (-61)) (.leaf (-62)))),
  (.branch 11 (.leaf (0)) (.leaf (-23)))]
  high := ![(.branch 57 (.branch 45 (.branch 41 (.leaf (-29)) (.leaf (-28))) (.branch 49 (.leaf (-27)) (.branch 53 (.leaf (-26)) (.leaf (-25))))) (.branch 69 (.branch 61 (.leaf (-24)) (.branch 65 (.leaf (-23)) (.leaf (-22)))) (.branch 73 (.leaf (-21)) (.branch 77 (.leaf (-20)) (.leaf (-10)))))),
  (.branch 75 (.branch 74 (.leaf (-10)) (.leaf (-8))) (.branch 76 (.leaf (-6)) (.branch 77 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-3)),
  (.branch 73 (.branch 71 (.branch 60 (.leaf (-29)) (.leaf (-28))) (.branch 72 (.leaf (-26)) (.leaf (-24)))) (.branch 75 (.branch 74 (.leaf (-22)) (.leaf (-20))) (.branch 76 (.leaf (-18)) (.branch 77 (.leaf (-16)) (.leaf (-14)))))),
  (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 74 (.branch 72 (.branch 58 (.leaf (-8)) (.leaf (-7))) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.branch 71 (.branch 68 (.branch 51 (.leaf (-62)) (.branch 67 (.leaf (-60)) (.leaf (-55)))) (.branch 69 (.leaf (-50)) (.branch 70 (.leaf (-45)) (.leaf (-40))))) (.branch 74 (.branch 72 (.leaf (-35)) (.branch 73 (.leaf (-30)) (.leaf (-25)))) (.branch 76 (.branch 75 (.leaf (-20)) (.leaf (-15))) (.branch 77 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 75 (.branch 12 (.leaf (-23)) (.branch 59 (.leaf (-22)) (.leaf (-20)))) (.branch 76 (.leaf (-15)) (.branch 77 (.leaf (-10)) (.leaf (-5)))))]
def witnessP9_271_4172 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (8)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (2))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (3)) (.leaf (6))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (4))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (5))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (7)) (.leaf (1))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (8)) (.leaf (4))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (5)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (6)) (.leaf (2))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (7)) (.leaf (4))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (5)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (8)) (.leaf (1))) (.branch 42 (.leaf (3)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (4))) (.branch 46 (.leaf (6)) (.branch 47 (.leaf (1)) (.leaf (0)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (5)) (.leaf (2))) (.branch 51 (.leaf (7)) (.branch 52 (.leaf (3)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (4))) (.branch 56 (.leaf (8)) (.branch 57 (.leaf (2)) (.leaf (5))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (6)) (.branch 62 (.leaf (3)) (.leaf (2))))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (4))) (.branch 66 (.leaf (7)) (.branch 67 (.leaf (1)) (.leaf (5)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (0)) (.leaf (2))) (.branch 71 (.leaf (3)) (.branch 72 (.leaf (8)) (.leaf (1))))) (.branch 75 (.branch 74 (.leaf (0)) (.leaf (4))) (.branch 76 (.leaf (2)) (.branch 77 (.leaf (6)) (.leaf (5)))))))))
  code := certificateP9_4172
  counts := ![(.branch 38 (.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))) (.branch 59 (.branch 48 (.branch 43 (.leaf (8)) (.leaf (9))) (.branch 53 (.leaf (10)) (.leaf (11)))) (.branch 69 (.branch 64 (.leaf (12)) (.leaf (13))) (.branch 74 (.leaf (14)) (.leaf (15)))))),
  (.branch 34 (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 54 (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))) (.branch 67 (.branch 60 (.leaf (9)) (.leaf (10))) (.branch 73 (.leaf (11)) (.leaf (12)))))),
  (.branch 37 (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))) (.branch 57 (.branch 44 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))) (.branch 70 (.branch 63 (.leaf (9)) (.leaf (10))) (.branch 76 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.branch 71 (.leaf (7)) (.leaf (8)))))),
  (.branch 36 (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 55 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 65 (.leaf (6)) (.branch 75 (.leaf (7)) (.leaf (8)))))),
  (.branch 39 (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 58 (.branch 49 (.leaf (4)) (.leaf (5))) (.branch 68 (.leaf (6)) (.branch 78 (.leaf (7)) (.leaf (8)))))),
  (.branch 46 (.branch 14 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 61 (.leaf (3)) (.branch 77 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 4 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 66 (.leaf (4)) (.leaf (5))))),
  (.branch 40 (.branch 9 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 56 (.leaf (3)) (.branch 72 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-21))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 32 (.leaf (-27)) (.leaf (-28)))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 19 (.leaf (0)) (.leaf (-2))),
  (.branch 14 (.leaf (0)) (.leaf (-8))),
  (.branch 35 (.branch 4 (.leaf (0)) (.leaf (-58))) (.branch 66 (.leaf (-59)) (.leaf (-60)))),
  (.branch 9 (.leaf (0)) (.branch 40 (.leaf (-33)) (.leaf (-34))))]
  high := ![(.branch 75 (.branch 54 (.leaf (-21)) (.leaf (-20))) (.branch 76 (.leaf (-15)) (.branch 77 (.leaf (-10)) (.leaf (-5))))),
  (.branch 75 (.branch 74 (.leaf (-10)) (.leaf (-8))) (.branch 76 (.leaf (-6)) (.branch 77 (.leaf (-4)) (.leaf (-2))))),
  (.branch 77 (.leaf (-4)) (.leaf (-2))),
  (.branch 74 (.branch 72 (.leaf (-28)) (.branch 73 (.leaf (-24)) (.leaf (-20)))) (.branch 76 (.branch 75 (.leaf (-16)) (.leaf (-12))) (.branch 77 (.leaf (-8)) (.leaf (-4))))),
  (.branch 66 (.branch 46 (.leaf (-15)) (.branch 56 (.leaf (-14)) (.leaf (-13)))) (.branch 76 (.leaf (-12)) (.branch 77 (.leaf (-8)) (.leaf (-4))))),
  (.branch 59 (.leaf (-2)) (.branch 69 (.leaf (-1)) (.leaf (0)))),
  (.branch 15 (.leaf (-8)) (.branch 62 (.leaf (-7)) (.leaf (-5)))),
  (.branch 72 (.branch 69 (.branch 67 (.leaf (-60)) (.branch 68 (.leaf (-55)) (.leaf (-50)))) (.branch 70 (.leaf (-45)) (.branch 71 (.leaf (-40)) (.leaf (-35))))) (.branch 75 (.branch 73 (.leaf (-30)) (.branch 74 (.leaf (-25)) (.leaf (-20)))) (.branch 76 (.leaf (-15)) (.branch 77 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 74 (.branch 57 (.branch 41 (.leaf (-34)) (.leaf (-32))) (.branch 73 (.leaf (-30)) (.leaf (-25)))) (.branch 76 (.branch 75 (.leaf (-20)) (.leaf (-15))) (.branch 77 (.leaf (-10)) (.leaf (-5)))))]
def witnessP9_271_4173 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (7)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (3)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (6))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (8))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (1))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (5)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (7))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (6))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (3)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (4)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (0))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (8)) (.leaf (0)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (5)) (.leaf (1))) (.branch 51 (.leaf (0)) (.branch 52 (.leaf (3)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (6))) (.branch 56 (.leaf (0)) (.branch 57 (.leaf (2)) (.leaf (0))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (1)) (.leaf (7))) (.branch 61 (.leaf (0)) (.branch 62 (.leaf (4)) (.leaf (1))))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (3))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (1)) (.leaf (5)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (0)) (.leaf (2))) (.branch 71 (.leaf (0)) (.branch 72 (.leaf (1)) (.leaf (8))))) (.branch 75 (.branch 74 (.leaf (0)) (.leaf (6))) (.branch 76 (.leaf (1)) (.branch 77 (.leaf (0)) (.leaf (3)))))))))
  code := certificateP9_4173
  counts := ![(.branch 38 (.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 22 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 25 (.leaf (9)) (.leaf (10)))) (.branch 32 (.branch 30 (.leaf (11)) (.leaf (12))) (.branch 35 (.leaf (13)) (.leaf (14)))))) (.branch 58 (.branch 48 (.branch 43 (.branch 40 (.leaf (15)) (.leaf (16))) (.branch 45 (.leaf (17)) (.leaf (18)))) (.branch 53 (.branch 51 (.leaf (19)) (.leaf (20))) (.branch 56 (.leaf (21)) (.leaf (22))))) (.branch 69 (.branch 64 (.branch 61 (.leaf (23)) (.leaf (24))) (.branch 66 (.leaf (25)) (.leaf (26)))) (.branch 74 (.branch 71 (.leaf (27)) (.leaf (28))) (.branch 77 (.leaf (29)) (.leaf (30))))))),
  (.branch 37 (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))) (.branch 59 (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.branch 54 (.leaf (12)) (.leaf (13))))) (.branch 67 (.branch 63 (.leaf (14)) (.leaf (15))) (.branch 72 (.leaf (16)) (.branch 76 (.leaf (17)) (.leaf (18))))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 70 (.leaf (5)) (.leaf (6))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 65 (.branch 52 (.leaf (3)) (.leaf (4))) (.branch 78 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 68 (.leaf (3)) (.leaf (4))))),
  (.branch 36 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.branch 75 (.leaf (3)) (.leaf (4))))),
  (.branch 34 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 47 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 73 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-33))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (-19)) (.leaf (-20)))),
  (.branch 16 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 72 (.leaf (-9)) (.branch 75 (.leaf (-7)) (.leaf (-5)))),
  (.branch 68 (.leaf (-7)) (.branch 77 (.leaf (-6)) (.leaf (-3)))),
  (.branch 74 (.branch 72 (.branch 71 (.leaf (-8)) (.leaf (-7))) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 69 (.branch 65 (.branch 63 (.branch 43 (.leaf (-33)) (.leaf (-32))) (.branch 64 (.leaf (-30)) (.leaf (-28)))) (.branch 67 (.branch 66 (.leaf (-26)) (.leaf (-24))) (.branch 68 (.leaf (-22)) (.leaf (-20))))) (.branch 73 (.branch 71 (.branch 70 (.leaf (-18)) (.leaf (-16))) (.branch 72 (.leaf (-14)) (.leaf (-12)))) (.branch 75 (.branch 74 (.leaf (-10)) (.leaf (-8))) (.branch 76 (.leaf (-6)) (.branch 77 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 73 (.branch 70 (.branch 69 (.leaf (-20)) (.leaf (-18))) (.branch 71 (.leaf (-16)) (.branch 72 (.leaf (-14)) (.leaf (-12))))) (.branch 75 (.branch 74 (.leaf (-10)) (.leaf (-8))) (.branch 76 (.leaf (-6)) (.branch 77 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 76 (.branch 56 (.leaf (-7)) (.leaf (-6))) (.branch 77 (.leaf (-4)) (.leaf (-2)))),
  (.branch 69 (.branch 64 (.branch 62 (.branch 61 (.leaf (-18)) (.leaf (-17))) (.branch 63 (.leaf (-16)) (.leaf (-15)))) (.branch 66 (.branch 65 (.leaf (-14)) (.leaf (-13))) (.branch 67 (.leaf (-12)) (.branch 68 (.leaf (-11)) (.leaf (-10)))))) (.branch 73 (.branch 71 (.branch 70 (.leaf (-9)) (.leaf (-8))) (.branch 72 (.leaf (-7)) (.leaf (-6)))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_271_4174 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (6)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (5))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (3)) (.leaf (0))) (.branch 22 (.leaf (7)) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (3))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (4)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (3)) (.leaf (0))))) (.branch 36 (.branch 35 (.leaf (8)) (.leaf (1))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (3)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (5)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (1))) (.branch 46 (.leaf (3)) (.branch 47 (.leaf (0)) (.leaf (6)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (4))) (.branch 56 (.leaf (0)) (.branch 57 (.leaf (2)) (.leaf (1))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (3)) (.leaf (0))) (.branch 61 (.leaf (7)) (.branch 62 (.leaf (1)) (.leaf (0))))) (.branch 65 (.branch 64 (.leaf (2)) (.leaf (3))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (1)) (.leaf (5)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (0)) (.leaf (2))) (.branch 71 (.leaf (1)) (.branch 72 (.leaf (3)) (.leaf (0))))) (.branch 75 (.branch 74 (.leaf (8)) (.leaf (1))) (.branch 76 (.leaf (0)) (.branch 77 (.leaf (2)) (.leaf (3)))))))))
  code := certificateP9_4174
  counts := ![(.branch 37 (.branch 17 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 30 (.leaf (9)) (.branch 34 (.leaf (10)) (.leaf (11)))))) (.branch 56 (.branch 47 (.branch 40 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14)))) (.branch 50 (.leaf (15)) (.branch 53 (.leaf (16)) (.leaf (17))))) (.branch 66 (.branch 60 (.leaf (18)) (.branch 63 (.leaf (19)) (.leaf (20)))) (.branch 73 (.branch 69 (.leaf (21)) (.leaf (22))) (.branch 76 (.leaf (23)) (.leaf (24))))))),
  (.branch 36 (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))) (.branch 58 (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.branch 54 (.leaf (12)) (.leaf (13))))) (.branch 67 (.branch 62 (.leaf (14)) (.leaf (15))) (.branch 71 (.leaf (16)) (.branch 75 (.leaf (17)) (.leaf (18))))))),
  (.branch 38 (.branch 18 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))) (.branch 57 (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))) (.branch 70 (.branch 64 (.leaf (9)) (.leaf (10))) (.branch 77 (.leaf (11)) (.leaf (12)))))),
  (.branch 39 (.branch 20 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))) (.branch 59 (.branch 46 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))) (.branch 72 (.branch 65 (.leaf (9)) (.leaf (10))) (.branch 78 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 68 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 61 (.leaf (1)) (.leaf (2)))),
  (.branch 35 (.leaf (0)) (.branch 74 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 16 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.leaf (0)) (.leaf (-30))),
  (.branch 22 (.leaf (0)) (.leaf (-17))),
  (.branch 35 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 70 (.leaf (-10)) (.branch 77 (.leaf (-8)) (.leaf (-4)))),
  (.branch 76 (.leaf (-9)) (.branch 77 (.leaf (-6)) (.leaf (-3)))),
  (.branch 71 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 66 (.branch 60 (.branch 57 (.branch 56 (.leaf (-23)) (.leaf (-22))) (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-20)) (.leaf (-19))))) (.branch 63 (.branch 61 (.leaf (-18)) (.branch 62 (.leaf (-17)) (.leaf (-16)))) (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-14)) (.leaf (-13)))))) (.branch 72 (.branch 69 (.branch 67 (.leaf (-12)) (.branch 68 (.leaf (-11)) (.leaf (-10)))) (.branch 70 (.leaf (-9)) (.branch 71 (.leaf (-8)) (.leaf (-7))))) (.branch 75 (.branch 73 (.leaf (-6)) (.branch 74 (.leaf (-5)) (.leaf (-4)))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 73 (.branch 70 (.branch 69 (.leaf (-10)) (.leaf (-9))) (.branch 71 (.leaf (-8)) (.branch 72 (.leaf (-7)) (.leaf (-6))))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 55 (.branch 51 (.branch 49 (.leaf (-30)) (.branch 50 (.leaf (-29)) (.leaf (-28)))) (.branch 53 (.branch 52 (.leaf (-27)) (.leaf (-26))) (.branch 54 (.leaf (-25)) (.leaf (-24))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-23)) (.leaf (-22))) (.branch 58 (.leaf (-21)) (.leaf (-20)))) (.branch 61 (.branch 60 (.leaf (-19)) (.leaf (-18))) (.branch 62 (.leaf (-17)) (.leaf (-16)))))) (.branch 70 (.branch 66 (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-14)) (.leaf (-13)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-11))) (.branch 69 (.leaf (-10)) (.leaf (-9))))) (.branch 74 (.branch 72 (.branch 71 (.leaf (-8)) (.leaf (-7))) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 69 (.branch 65 (.branch 63 (.branch 62 (.leaf (-17)) (.leaf (-16))) (.branch 64 (.leaf (-15)) (.leaf (-14)))) (.branch 67 (.branch 66 (.leaf (-13)) (.leaf (-12))) (.branch 68 (.leaf (-11)) (.leaf (-10))))) (.branch 73 (.branch 71 (.branch 70 (.leaf (-9)) (.leaf (-8))) (.branch 72 (.leaf (-7)) (.leaf (-6)))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_271_4175 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (5))) (.branch 7 (.leaf (7)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (8)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (3)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (7)) (.leaf (6))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (8))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (3)) (.leaf (5)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (0))))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (4))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (8)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (5)) (.leaf (1))) (.branch 42 (.leaf (0)) (.leaf (6)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (0))) (.branch 46 (.leaf (7)) (.branch 47 (.leaf (4)) (.leaf (3)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (5)) (.branch 52 (.leaf (8)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (6))) (.branch 56 (.leaf (0)) (.branch 57 (.leaf (3)) (.leaf (4))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (7)) (.leaf (0))) (.branch 61 (.leaf (1)) (.branch 62 (.leaf (5)) (.leaf (2))))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (8))) (.branch 66 (.leaf (6)) (.branch 67 (.leaf (3)) (.leaf (0)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (4)) (.leaf (1))) (.branch 71 (.leaf (0)) (.branch 72 (.leaf (7)) (.leaf (5))))) (.branch 75 (.branch 74 (.leaf (2)) (.leaf (0))) (.branch 76 (.leaf (3)) (.branch 77 (.leaf (6)) (.leaf (8)))))))))
  code := certificateP9_4175
  counts := ![(.branch 38 (.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))) (.branch 56 (.branch 45 (.branch 42 (.leaf (11)) (.leaf (12))) (.branch 49 (.leaf (13)) (.branch 53 (.leaf (14)) (.leaf (15))))) (.branch 68 (.branch 60 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18)))) (.branch 71 (.leaf (19)) (.branch 75 (.leaf (20)) (.leaf (21))))))),
  (.branch 31 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.branch 70 (.leaf (7)) (.leaf (8)))))),
  (.branch 35 (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.branch 74 (.leaf (7)) (.leaf (8)))))),
  (.branch 37 (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 57 (.branch 48 (.leaf (4)) (.leaf (5))) (.branch 67 (.leaf (6)) (.branch 76 (.leaf (7)) (.leaf (8)))))),
  (.branch 36 (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 58 (.branch 47 (.leaf (4)) (.leaf (5))) (.branch 69 (.leaf (6)) (.leaf (7))))),
  (.branch 40 (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 62 (.branch 51 (.leaf (4)) (.leaf (5))) (.branch 73 (.leaf (6)) (.leaf (7))))),
  (.branch 43 (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))) (.branch 66 (.branch 55 (.leaf (4)) (.leaf (5))) (.branch 77 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 59 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 72 (.leaf (5)) (.leaf (6))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 65 (.branch 52 (.leaf (3)) (.leaf (4))) (.branch 78 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-19)) (.leaf (-24)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 50 (.leaf (-9)) (.leaf (-10)))),
  (.branch 24 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 63 (.leaf (-6)) (.leaf (-7)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (-1))) (.branch 37 (.leaf (-2)) (.branch 76 (.leaf (-3)) (.leaf (-4))))),
  (.branch 36 (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-57))) (.branch 25 (.leaf (-58)) (.leaf (-59)))) (.branch 58 (.branch 47 (.leaf (-60)) (.leaf (-61))) (.branch 69 (.leaf (-62)) (.leaf (-63))))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-36)) (.leaf (-37)))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (-8))) (.branch 32 (.leaf (-9)) (.branch 43 (.leaf (-10)) (.leaf (-11))))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 72 (.branch 57 (.leaf (-24)) (.leaf (-23))) (.branch 76 (.leaf (-21)) (.branch 77 (.leaf (-14)) (.leaf (-7))))),
  (.branch 74 (.branch 72 (.branch 71 (.leaf (-10)) (.leaf (-9))) (.branch 73 (.leaf (-8)) (.leaf (-7)))) (.branch 76 (.branch 75 (.leaf (-6)) (.leaf (-5))) (.branch 77 (.leaf (-4)) (.leaf (-3))))),
  (.branch 75 (.branch 64 (.leaf (-7)) (.leaf (-6))) (.branch 76 (.leaf (-5)) (.branch 77 (.leaf (-4)) (.leaf (-3))))),
  (.branch 77 (.leaf (-4)) (.leaf (-3))),
  (.branch 73 (.branch 71 (.branch 70 (.leaf (-63)) (.leaf (-56))) (.branch 72 (.leaf (-49)) (.leaf (-42)))) (.branch 75 (.branch 74 (.leaf (-35)) (.leaf (-28))) (.branch 76 (.leaf (-21)) (.branch 77 (.leaf (-14)) (.leaf (-7)))))),
  (.branch 75 (.branch 18 (.leaf (-37)) (.branch 74 (.leaf (-35)) (.leaf (-28)))) (.branch 76 (.leaf (-21)) (.branch 77 (.leaf (-14)) (.leaf (-7))))),
  (.branch 44 (.leaf (-11)) (.leaf (-7))),
  (.branch 75 (.branch 73 (.leaf (-6)) (.branch 74 (.leaf (-5)) (.leaf (-4)))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessP9_271_4176 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (6))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (3)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (4))) (.branch 12 (.leaf (7)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (5))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (6))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (4)) (.leaf (2))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (5))))) (.branch 26 (.branch 25 (.leaf (8)) (.leaf (1))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (4)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (3))) (.branch 32 (.leaf (6)) (.branch 33 (.leaf (5)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (4)) (.branch 38 (.leaf (7)) (.leaf (3)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (5)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (6))) (.branch 46 (.leaf (4)) (.branch 47 (.leaf (3)) (.leaf (0)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (5))) (.branch 51 (.leaf (8)) (.branch 52 (.leaf (2)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (0)) (.branch 57 (.leaf (1)) (.leaf (6))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (5)) (.leaf (2))) (.branch 61 (.leaf (0)) (.branch 62 (.leaf (3)) (.leaf (4))))) (.branch 65 (.branch 64 (.leaf (7)) (.leaf (1))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (2)) (.leaf (5)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (0)) (.leaf (3))) (.branch 71 (.leaf (6)) (.branch 72 (.leaf (4)) (.leaf (1))))) (.branch 75 (.branch 74 (.leaf (0)) (.leaf (2))) (.branch 76 (.leaf (5)) (.branch 77 (.leaf (8)) (.leaf (3)))))))))
  code := certificateP9_4176
  counts := ![(.branch 35 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))) (.branch 56 (.branch 43 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.branch 53 (.leaf (12)) (.leaf (13))))) (.branch 66 (.branch 61 (.leaf (14)) (.leaf (15))) (.branch 69 (.leaf (16)) (.branch 74 (.leaf (17)) (.leaf (18))))))),
  (.branch 34 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 57 (.branch 41 (.leaf (5)) (.branch 49 (.leaf (6)) (.leaf (7)))) (.branch 65 (.leaf (8)) (.branch 73 (.leaf (9)) (.leaf (10)))))),
  (.branch 36 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 60 (.branch 44 (.leaf (5)) (.branch 52 (.leaf (6)) (.leaf (7)))) (.branch 67 (.leaf (8)) (.branch 75 (.leaf (9)) (.leaf (10)))))),
  (.branch 39 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))) (.branch 62 (.branch 47 (.leaf (5)) (.branch 54 (.leaf (6)) (.leaf (7)))) (.branch 70 (.leaf (8)) (.branch 78 (.leaf (9)) (.leaf (10)))))),
  (.branch 37 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 55 (.branch 46 (.leaf (5)) (.leaf (6))) (.branch 63 (.leaf (7)) (.branch 72 (.leaf (8)) (.leaf (9)))))),
  (.branch 42 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))) (.branch 59 (.branch 50 (.leaf (5)) (.leaf (6))) (.branch 68 (.leaf (7)) (.branch 76 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 58 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 71 (.leaf (5)) (.leaf (6))))),
  (.branch 38 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3)))),
  (.branch 51 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 77 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 30 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-10)) (.leaf (-11)))) (.branch 56 (.branch 43 (.leaf (-12)) (.leaf (-13))) (.branch 69 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.leaf (-29))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-14)) (.leaf (-16)))),
  (.branch 15 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-19)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-14))),
  (.branch 25 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 75 (.branch 70 (.leaf (-15)) (.leaf (-14))) (.branch 76 (.leaf (-12)) (.branch 77 (.leaf (-10)) (.leaf (-8))))),
  (.branch 66 (.branch 50 (.branch 42 (.leaf (-29)) (.leaf (-28))) (.branch 58 (.leaf (-27)) (.leaf (-26)))) (.branch 75 (.branch 74 (.leaf (-25)) (.leaf (-20))) (.branch 76 (.leaf (-15)) (.branch 77 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 76 (.branch 68 (.leaf (-16)) (.leaf (-15))) (.branch 77 (.leaf (-10)) (.leaf (-5)))),
  (.branch 63 (.branch 55 (.leaf (-3)) (.leaf (-2))) (.branch 71 (.leaf (-1)) (.leaf (0)))),
  (.branch 74 (.branch 64 (.leaf (-19)) (.branch 73 (.leaf (-18)) (.leaf (-15)))) (.branch 76 (.branch 75 (.leaf (-12)) (.leaf (-9))) (.branch 77 (.leaf (-6)) (.leaf (-3))))),
  (.branch 77 (.leaf (-6)) (.leaf (-3))),
  (.branch 74 (.branch 72 (.leaf (-7)) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.branch 71 (.branch 67 (.branch 65 (.leaf (-14)) (.branch 66 (.leaf (-13)) (.leaf (-12)))) (.branch 69 (.branch 68 (.leaf (-11)) (.leaf (-10))) (.branch 70 (.leaf (-9)) (.leaf (-8))))) (.branch 74 (.branch 72 (.leaf (-7)) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_271_4177 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (7)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (4))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (8)) (.leaf (2))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 25 (.leaf (5)) (.leaf (2))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (3)) (.leaf (4)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (7)) (.leaf (3))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (6)) (.leaf (3)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (4)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (3))) (.branch 46 (.leaf (8)) (.branch 47 (.leaf (1)) (.leaf (2)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (5)) (.branch 52 (.leaf (1)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (4))) (.branch 56 (.leaf (3)) (.branch 57 (.leaf (0)) (.leaf (1))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (7)) (.leaf (2))) (.branch 61 (.leaf (3)) (.branch 62 (.leaf (0)) (.leaf (1))))) (.branch 65 (.branch 64 (.leaf (6)) (.leaf (2))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (3)) (.leaf (4)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (1)) (.leaf (0))) (.branch 71 (.leaf (2)) (.branch 72 (.leaf (8)) (.leaf (3))))) (.branch 75 (.branch 74 (.leaf (1)) (.leaf (0))) (.branch 76 (.leaf (2)) (.branch 77 (.leaf (5)) (.leaf (3)))))))))
  code := certificateP9_4177
  counts := ![(.branch 36 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))) (.branch 57 (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.branch 53 (.leaf (12)) (.leaf (13))))) (.branch 66 (.branch 62 (.leaf (14)) (.leaf (15))) (.branch 70 (.leaf (16)) (.branch 75 (.leaf (17)) (.leaf (18))))))),
  (.branch 35 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))) (.branch 58 (.branch 47 (.branch 41 (.leaf (7)) (.leaf (8))) (.branch 52 (.leaf (9)) (.leaf (10)))) (.branch 69 (.branch 63 (.leaf (11)) (.leaf (12))) (.branch 74 (.leaf (13)) (.leaf (14)))))),
  (.branch 37 (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))) (.branch 60 (.branch 48 (.branch 43 (.leaf (7)) (.leaf (8))) (.branch 54 (.leaf (9)) (.leaf (10)))) (.branch 71 (.branch 65 (.leaf (11)) (.leaf (12))) (.branch 76 (.leaf (13)) (.leaf (14)))))),
  (.branch 39 (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))) (.branch 61 (.branch 50 (.branch 45 (.leaf (7)) (.leaf (8))) (.branch 56 (.leaf (9)) (.leaf (10)))) (.branch 73 (.branch 67 (.leaf (11)) (.leaf (12))) (.branch 78 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 51 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 77 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 46 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 72 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-25))) (.branch 24 (.leaf (-26)) (.branch 35 (.leaf (-27)) (.leaf (-28))))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-15)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-14))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 76 (.branch 71 (.leaf (-11)) (.leaf (-9))) (.branch 77 (.leaf (-6)) (.leaf (-3)))),
  (.branch 76 (.branch 75 (.leaf (-28)) (.leaf (-21))) (.branch 77 (.leaf (-14)) (.leaf (-7)))),
  (.branch 49 (.leaf (-15)) (.branch 77 (.leaf (-14)) (.leaf (-7)))),
  (.branch 62 (.leaf (-2)) (.leaf (0))),
  (.branch 73 (.branch 70 (.branch 69 (.leaf (-10)) (.leaf (-9))) (.branch 71 (.leaf (-8)) (.branch 72 (.leaf (-7)) (.leaf (-6))))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 71 (.branch 67 (.branch 65 (.leaf (-14)) (.branch 66 (.leaf (-13)) (.leaf (-12)))) (.branch 69 (.branch 68 (.leaf (-11)) (.leaf (-10))) (.branch 70 (.leaf (-9)) (.leaf (-8))))) (.branch 74 (.branch 72 (.leaf (-7)) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 68 (.branch 63 (.branch 61 (.branch 60 (.leaf (-19)) (.leaf (-18))) (.branch 62 (.leaf (-17)) (.leaf (-16)))) (.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-14))) (.branch 66 (.leaf (-13)) (.branch 67 (.leaf (-12)) (.leaf (-11)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (-10)) (.leaf (-9))) (.branch 71 (.leaf (-8)) (.branch 72 (.leaf (-7)) (.leaf (-6))))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 75 (.branch 73 (.leaf (-6)) (.branch 74 (.leaf (-5)) (.leaf (-4)))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_271_4178 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (5)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (7)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (5))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (6))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (2)) (.leaf (4))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (5))))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (8))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (4)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (3)) (.leaf (0))) (.branch 32 (.leaf (6)) (.branch 33 (.leaf (1)) (.leaf (5))))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (4)) (.branch 38 (.leaf (3)) (.leaf (7)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (5)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (6))) (.branch 46 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (1)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (2)) (.branch 52 (.leaf (8)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (1)) (.branch 57 (.leaf (0)) (.leaf (6))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (2)) (.leaf (5))) (.branch 61 (.leaf (3)) (.branch 62 (.leaf (0)) (.leaf (4))))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (7))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (2)) (.leaf (5)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (3)) (.leaf (0))) (.branch 71 (.leaf (6)) (.branch 72 (.leaf (1)) (.leaf (4))))) (.branch 75 (.branch 74 (.leaf (2)) (.leaf (0))) (.branch 76 (.leaf (5)) (.branch 77 (.leaf (3)) (.leaf (8)))))))))
  code := certificateP9_4178
  counts := ![(.branch 36 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))) (.branch 57 (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.branch 53 (.leaf (12)) (.leaf (13))))) (.branch 66 (.branch 62 (.leaf (14)) (.leaf (15))) (.branch 70 (.leaf (16)) (.branch 75 (.leaf (17)) (.leaf (18))))))),
  (.branch 33 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 56 (.branch 41 (.leaf (5)) (.branch 48 (.leaf (6)) (.leaf (7)))) (.branch 64 (.leaf (8)) (.branch 72 (.leaf (9)) (.leaf (10)))))),
  (.branch 35 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 59 (.branch 43 (.leaf (5)) (.branch 51 (.leaf (6)) (.leaf (7)))) (.branch 67 (.leaf (8)) (.branch 74 (.leaf (9)) (.leaf (10)))))),
  (.branch 38 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))) (.branch 61 (.branch 46 (.leaf (5)) (.branch 54 (.leaf (6)) (.leaf (7)))) (.branch 69 (.leaf (8)) (.branch 77 (.leaf (9)) (.leaf (10)))))),
  (.branch 37 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 55 (.branch 47 (.leaf (5)) (.leaf (6))) (.branch 63 (.leaf (7)) (.branch 73 (.leaf (8)) (.leaf (9)))))),
  (.branch 42 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))) (.branch 60 (.branch 50 (.leaf (5)) (.leaf (6))) (.branch 68 (.leaf (7)) (.branch 76 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 58 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 71 (.leaf (5)) (.leaf (6))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (2)) (.leaf (3)))),
  (.branch 52 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 78 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-29)) (.leaf (-33)))),
  (.branch 4 (.leaf (0)) (.branch 35 (.leaf (-19)) (.leaf (-20)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (-4)) (.leaf (-7)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 37 (.leaf (-7)) (.branch 63 (.leaf (-8)) (.leaf (-9))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))) (.branch 50 (.leaf (-3)) (.branch 76 (.leaf (-4)) (.leaf (-5))))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 76 (.branch 71 (.leaf (-11)) (.leaf (-9))) (.branch 77 (.leaf (-6)) (.leaf (-3)))),
  (.branch 73 (.branch 57 (.branch 49 (.leaf (-33)) (.leaf (-32))) (.branch 65 (.leaf (-31)) (.leaf (-30)))) (.branch 75 (.branch 74 (.leaf (-25)) (.leaf (-20))) (.branch 76 (.leaf (-15)) (.branch 77 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 76 (.branch 75 (.leaf (-20)) (.leaf (-15))) (.branch 77 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.leaf (-7)) (.branch 70 (.leaf (-6)) (.leaf (-5)))),
  (.branch 75 (.branch 64 (.leaf (-9)) (.branch 74 (.leaf (-8)) (.leaf (-7)))) (.branch 76 (.leaf (-6)) (.branch 77 (.leaf (-5)) (.leaf (-4))))),
  (.branch 77 (.leaf (-5)) (.leaf (-4))),
  (.branch 74 (.branch 72 (.leaf (-7)) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.branch 71 (.branch 68 (.branch 66 (.leaf (-13)) (.branch 67 (.leaf (-12)) (.leaf (-11)))) (.branch 69 (.leaf (-10)) (.branch 70 (.leaf (-9)) (.leaf (-8))))) (.branch 74 (.branch 72 (.leaf (-7)) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_271_4179 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (4)) (.leaf (7))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (0))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (5))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (6)) (.leaf (0))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (1)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (8)) (.branch 28 (.leaf (5)) (.leaf (1)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (6)) (.leaf (3))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (5)) (.leaf (7)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (4)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (3)) (.leaf (0))) (.branch 46 (.leaf (6)) (.branch 47 (.leaf (1)) (.leaf (5)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (1)) (.branch 52 (.leaf (4)) (.leaf (8))))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (0))) (.branch 56 (.leaf (2)) (.branch 57 (.leaf (1)) (.leaf (5))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (6)) (.leaf (0))) (.branch 61 (.leaf (4)) (.branch 62 (.leaf (1)) (.leaf (2))))) (.branch 65 (.branch 64 (.leaf (3)) (.leaf (0))) (.branch 66 (.leaf (7)) (.branch 67 (.leaf (5)) (.leaf (1)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (2)) (.leaf (0))) (.branch 71 (.leaf (4)) (.branch 72 (.leaf (6)) (.leaf (3))))) (.branch 75 (.branch 74 (.leaf (1)) (.leaf (0))) (.branch 76 (.leaf (2)) (.branch 77 (.leaf (5)) (.leaf (8)))))))))
  code := certificateP9_4179
  counts := ![(.branch 36 (.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))) (.branch 55 (.branch 45 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 50 (.leaf (10)) (.leaf (11)))) (.branch 65 (.branch 60 (.leaf (12)) (.leaf (13))) (.branch 70 (.leaf (14)) (.branch 75 (.leaf (15)) (.leaf (16))))))),
  (.branch 35 (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))) (.branch 57 (.branch 47 (.branch 41 (.leaf (7)) (.leaf (8))) (.branch 51 (.leaf (9)) (.leaf (10)))) (.branch 68 (.branch 62 (.leaf (11)) (.leaf (12))) (.branch 74 (.leaf (13)) (.leaf (14)))))),
  (.branch 37 (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))) (.branch 56 (.branch 43 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))) (.branch 69 (.branch 63 (.leaf (9)) (.leaf (10))) (.branch 76 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 64 (.leaf (6)) (.branch 73 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.branch 71 (.leaf (7)) (.leaf (8)))))),
  (.branch 38 (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 58 (.branch 48 (.leaf (4)) (.leaf (5))) (.branch 67 (.leaf (6)) (.branch 77 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 59 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 72 (.leaf (5)) (.leaf (6))))),
  (.branch 39 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3)))),
  (.branch 53 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 78 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-31))),
  (.branch 23 (.branch 2 (.leaf (0)) (.branch 12 (.leaf (-15)) (.leaf (-21)))) (.branch 51 (.leaf (-23)) (.branch 62 (.leaf (-26)) (.leaf (-28))))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.branch 34 (.leaf (-19)) (.leaf (-20)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-27)) (.leaf (-29)))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 14 (.leaf (0)) (.branch 39 (.leaf (-12)) (.leaf (-13)))),
  (.leaf (0))]
  high := ![(.branch 61 (.branch 46 (.branch 41 (.leaf (-31)) (.leaf (-30))) (.branch 51 (.leaf (-29)) (.branch 56 (.leaf (-28)) (.leaf (-27))))) (.branch 71 (.branch 66 (.leaf (-26)) (.leaf (-25))) (.branch 76 (.leaf (-24)) (.branch 77 (.leaf (-16)) (.leaf (-8)))))),
  (.branch 75 (.branch 63 (.leaf (-28)) (.branch 69 (.leaf (-27)) (.leaf (-26)))) (.branch 76 (.leaf (-22)) (.branch 77 (.leaf (-18)) (.leaf (-14))))),
  (.branch 70 (.branch 50 (.leaf (-6)) (.leaf (-5))) (.branch 77 (.leaf (-4)) (.leaf (-2)))),
  (.branch 75 (.branch 74 (.leaf (-20)) (.leaf (-16))) (.branch 76 (.leaf (-12)) (.branch 77 (.leaf (-8)) (.leaf (-4))))),
  (.branch 74 (.branch 72 (.branch 62 (.leaf (-29)) (.leaf (-28))) (.branch 73 (.leaf (-24)) (.leaf (-20)))) (.branch 76 (.branch 75 (.leaf (-16)) (.leaf (-12))) (.branch 77 (.leaf (-8)) (.leaf (-4))))),
  (.branch 68 (.leaf (-5)) (.leaf (-4))),
  (.branch 75 (.branch 73 (.leaf (-6)) (.branch 74 (.leaf (-5)) (.leaf (-4)))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.branch 71 (.branch 68 (.branch 40 (.leaf (-13)) (.branch 67 (.leaf (-12)) (.leaf (-11)))) (.branch 69 (.leaf (-10)) (.branch 70 (.leaf (-9)) (.leaf (-8))))) (.branch 74 (.branch 72 (.leaf (-7)) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_271_4180 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (6)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (4))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (3)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (5))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (3)) (.leaf (2))) (.branch 22 (.leaf (7)) (.branch 23 (.leaf (0)) (.leaf (5))))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (3))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (0)) (.leaf (4)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (5))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (0))))) (.branch 36 (.branch 35 (.leaf (8)) (.leaf (1))) (.branch 37 (.leaf (4)) (.branch 38 (.leaf (2)) (.leaf (3)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (5)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (4)) (.leaf (0))) (.branch 46 (.leaf (3)) (.branch 47 (.leaf (1)) (.leaf (6)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (2)) (.leaf (5))) (.branch 51 (.leaf (0)) (.branch 52 (.leaf (3)) (.leaf (1))))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (4))) (.branch 56 (.leaf (0)) (.branch 57 (.leaf (5)) (.leaf (1))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (3)) (.leaf (2))) (.branch 61 (.leaf (7)) (.branch 62 (.leaf (0)) (.leaf (4))))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (3))) (.branch 66 (.leaf (2)) (.branch 67 (.leaf (0)) (.leaf (5)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (1)) (.leaf (4))) (.branch 71 (.leaf (2)) (.branch 72 (.leaf (3)) (.leaf (0))))) (.branch 75 (.branch 74 (.leaf (8)) (.leaf (1))) (.branch 76 (.leaf (5)) (.branch 77 (.leaf (2)) (.leaf (3)))))))))
  code := certificateP9_4180
  counts := ![(.branch 34 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))) (.branch 56 (.branch 45 (.branch 40 (.leaf (7)) (.leaf (8))) (.branch 51 (.leaf (9)) (.leaf (10)))) (.branch 67 (.branch 62 (.leaf (11)) (.leaf (12))) (.branch 73 (.leaf (13)) (.leaf (14)))))),
  (.branch 36 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))) (.branch 58 (.branch 47 (.branch 41 (.leaf (7)) (.leaf (8))) (.branch 53 (.leaf (9)) (.leaf (10)))) (.branch 69 (.branch 64 (.leaf (11)) (.leaf (12))) (.branch 75 (.leaf (13)) (.leaf (14)))))),
  (.branch 38 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))) (.branch 60 (.branch 49 (.branch 43 (.leaf (7)) (.leaf (8))) (.branch 54 (.leaf (9)) (.leaf (10)))) (.branch 71 (.branch 66 (.leaf (11)) (.leaf (12))) (.branch 77 (.leaf (13)) (.leaf (14)))))),
  (.branch 39 (.branch 20 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))) (.branch 59 (.branch 46 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))) (.branch 72 (.branch 65 (.leaf (9)) (.leaf (10))) (.branch 78 (.leaf (11)) (.leaf (12)))))),
  (.branch 37 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 55 (.branch 44 (.leaf (5)) (.leaf (6))) (.branch 63 (.leaf (7)) (.branch 70 (.leaf (8)) (.leaf (9)))))),
  (.branch 42 (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))) (.branch 57 (.branch 50 (.leaf (5)) (.leaf (6))) (.branch 68 (.leaf (7)) (.branch 76 (.leaf (8)) (.leaf (9)))))),
  (.branch 9 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 61 (.leaf (1)) (.leaf (2)))),
  (.branch 35 (.leaf (0)) (.branch 74 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-32))) (.branch 17 (.leaf (-36)) (.branch 28 (.leaf (-37)) (.leaf (-38))))),
  (.branch 2 (.leaf (0)) (.leaf (-25))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 37 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 18 (.leaf (-9)) (.leaf (-12)))) (.branch 63 (.branch 44 (.leaf (-13)) (.leaf (-16))) (.branch 70 (.leaf (-17)) (.leaf (-20))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))) (.branch 57 (.branch 50 (.leaf (-9)) (.leaf (-10))) (.branch 76 (.leaf (-13)) (.leaf (-14))))),
  (.branch 9 (.leaf (0)) (.leaf (-30))),
  (.branch 22 (.leaf (0)) (.leaf (-17))),
  (.branch 35 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 75 (.branch 68 (.leaf (-38)) (.branch 74 (.leaf (-35)) (.leaf (-28)))) (.branch 76 (.leaf (-21)) (.branch 77 (.leaf (-14)) (.leaf (-7))))),
  (.branch 70 (.branch 42 (.leaf (-25)) (.leaf (-24))) (.branch 76 (.leaf (-21)) (.branch 77 (.leaf (-14)) (.leaf (-7))))),
  (.branch 55 (.leaf (-12)) (.branch 72 (.leaf (-10)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 74 (.branch 72 (.branch 71 (.leaf (-20)) (.leaf (-19))) (.branch 73 (.leaf (-18)) (.leaf (-17)))) (.branch 76 (.branch 75 (.leaf (-16)) (.leaf (-15))) (.branch 77 (.leaf (-14)) (.leaf (-13))))),
  (.branch 77 (.leaf (-14)) (.leaf (-13))),
  (.branch 63 (.branch 55 (.branch 51 (.branch 49 (.leaf (-30)) (.branch 50 (.leaf (-29)) (.leaf (-28)))) (.branch 53 (.branch 52 (.leaf (-27)) (.leaf (-26))) (.branch 54 (.leaf (-25)) (.leaf (-24))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-23)) (.leaf (-22))) (.branch 58 (.leaf (-21)) (.leaf (-20)))) (.branch 61 (.branch 60 (.leaf (-19)) (.leaf (-18))) (.branch 62 (.leaf (-17)) (.leaf (-16)))))) (.branch 70 (.branch 66 (.branch 64 (.leaf (-15)) (.branch 65 (.leaf (-14)) (.leaf (-13)))) (.branch 68 (.branch 67 (.leaf (-12)) (.leaf (-11))) (.branch 69 (.leaf (-10)) (.leaf (-9))))) (.branch 74 (.branch 72 (.branch 71 (.leaf (-8)) (.leaf (-7))) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 69 (.branch 65 (.branch 63 (.branch 62 (.leaf (-17)) (.leaf (-16))) (.branch 64 (.leaf (-15)) (.leaf (-14)))) (.branch 67 (.branch 66 (.leaf (-13)) (.leaf (-12))) (.branch 68 (.leaf (-11)) (.leaf (-10))))) (.branch 73 (.branch 71 (.branch 70 (.leaf (-9)) (.leaf (-8))) (.branch 72 (.leaf (-7)) (.leaf (-6)))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_271_4181 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (6)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (5)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (8))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (6))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (5))) (.branch 27 (.leaf (3)) (.branch 28 (.leaf (0)) (.leaf (1)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (7)) (.leaf (2))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (0)) (.leaf (6))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (2)) (.leaf (5)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (4)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (8)) (.leaf (0))) (.branch 46 (.leaf (3)) (.branch 47 (.leaf (1)) (.leaf (6)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (4)) (.branch 52 (.leaf (5)) (.leaf (1))))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (7))) (.branch 56 (.leaf (3)) (.branch 57 (.leaf (2)) (.leaf (0))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (1)) (.leaf (6))) (.branch 61 (.leaf (4)) (.branch 62 (.leaf (1)) (.leaf (0))))) (.branch 65 (.branch 64 (.leaf (2)) (.leaf (5))) (.branch 66 (.leaf (3)) (.branch 67 (.leaf (0)) (.leaf (1)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (8)) (.leaf (2))) (.branch 71 (.leaf (4)) (.branch 72 (.leaf (0)) (.leaf (6))))) (.branch 75 (.branch 74 (.leaf (1)) (.leaf (0))) (.branch 76 (.leaf (3)) (.branch 77 (.leaf (2)) (.leaf (5)))))))))
  code := certificateP9_4181
  counts := ![(.branch 36 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))) (.branch 58 (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.branch 54 (.leaf (12)) (.leaf (13))))) (.branch 67 (.branch 63 (.leaf (14)) (.leaf (15))) (.branch 72 (.leaf (16)) (.branch 75 (.leaf (17)) (.leaf (18))))))),
  (.branch 35 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))) (.branch 59 (.branch 47 (.branch 41 (.leaf (7)) (.leaf (8))) (.branch 53 (.leaf (9)) (.leaf (10)))) (.branch 68 (.branch 62 (.leaf (11)) (.leaf (12))) (.branch 74 (.leaf (13)) (.leaf (14)))))),
  (.branch 38 (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))) (.branch 57 (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))) (.branch 70 (.branch 64 (.leaf (9)) (.leaf (10))) (.branch 77 (.leaf (11)) (.leaf (12)))))),
  (.branch 37 (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 66 (.leaf (6)) (.branch 76 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.branch 71 (.leaf (7)) (.leaf (8)))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 65 (.branch 52 (.leaf (3)) (.leaf (4))) (.branch 78 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 60 (.branch 48 (.leaf (3)) (.leaf (4))) (.branch 73 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 69 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 36 (.branch 1 (.leaf (0)) (.leaf (-24))) (.branch 40 (.leaf (-27)) (.branch 75 (.leaf (-30)) (.leaf (-33))))),
  (.branch 23 (.branch 2 (.leaf (0)) (.leaf (-23))) (.branch 62 (.leaf (-37)) (.leaf (-48)))),
  (.branch 4 (.leaf (0)) (.branch 43 (.leaf (-8)) (.leaf (-11)))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-27)) (.leaf (-30)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (-4)) (.leaf (-5)))),
  (.branch 30 (.branch 5 (.leaf (0)) (.leaf (-22))) (.branch 55 (.leaf (-24)) (.leaf (-26)))),
  (.branch 16 (.leaf (0)) (.branch 69 (.leaf (-11)) (.leaf (-12))))]
  high := ![(.branch 76 (.leaf (-33)) (.branch 77 (.leaf (-26)) (.leaf (-19)))),
  (.branch 75 (.branch 63 (.leaf (-48)) (.branch 69 (.leaf (-47)) (.leaf (-46)))) (.branch 76 (.leaf (-40)) (.branch 77 (.leaf (-34)) (.leaf (-28))))),
  (.branch 44 (.leaf (-11)) (.branch 71 (.leaf (-10)) (.leaf (-9)))),
  (.branch 57 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 67 (.leaf (-9)) (.branch 77 (.leaf (-8)) (.leaf (-4))))),
  (.branch 73 (.branch 62 (.branch 52 (.leaf (-30)) (.leaf (-29))) (.branch 72 (.leaf (-28)) (.leaf (-24)))) (.branch 75 (.branch 74 (.leaf (-20)) (.leaf (-16))) (.branch 76 (.leaf (-12)) (.branch 77 (.leaf (-8)) (.leaf (-4)))))),
  (.leaf (0)),
  (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.branch 66 (.branch 60 (.branch 57 (.branch 56 (.leaf (-26)) (.leaf (-25))) (.branch 58 (.leaf (-24)) (.branch 59 (.leaf (-23)) (.leaf (-22))))) (.branch 63 (.branch 61 (.leaf (-21)) (.branch 62 (.leaf (-20)) (.leaf (-19)))) (.branch 64 (.leaf (-18)) (.branch 65 (.leaf (-17)) (.leaf (-16)))))) (.branch 72 (.branch 69 (.branch 67 (.leaf (-15)) (.branch 68 (.leaf (-14)) (.leaf (-13)))) (.branch 70 (.leaf (-12)) (.branch 71 (.leaf (-11)) (.leaf (-10))))) (.branch 75 (.branch 73 (.leaf (-9)) (.branch 74 (.leaf (-8)) (.leaf (-7)))) (.branch 76 (.leaf (-6)) (.branch 77 (.leaf (-5)) (.leaf (-4))))))),
  (.branch 73 (.branch 71 (.branch 70 (.leaf (-12)) (.leaf (-11))) (.branch 72 (.leaf (-10)) (.leaf (-9)))) (.branch 75 (.branch 74 (.leaf (-8)) (.leaf (-7))) (.branch 76 (.leaf (-6)) (.branch 77 (.leaf (-5)) (.leaf (-4))))))]
def witnessP9_271_4182 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (5))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (4))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (8)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (5))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (6)) (.leaf (2))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (4)) (.leaf (0))) (.branch 22 (.leaf (7)) (.branch 23 (.leaf (3)) (.leaf (5))))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (4)) (.leaf (6)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (8)) (.leaf (3))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (1)) (.leaf (0))))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (7))) (.branch 37 (.leaf (4)) (.branch 38 (.leaf (6)) (.leaf (3)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (5)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (8)) (.leaf (4))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (1)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (6)) (.leaf (5))) (.branch 51 (.leaf (2)) (.branch 52 (.leaf (7)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (1)) (.branch 57 (.leaf (6)) (.leaf (2))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (5)) (.leaf (0))) (.branch 61 (.leaf (8)) (.branch 62 (.leaf (3)) (.leaf (4))))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (0))) (.branch 66 (.leaf (2)) (.branch 67 (.leaf (5)) (.leaf (6)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (7)) (.leaf (3))) (.branch 71 (.leaf (4)) (.branch 72 (.leaf (1)) (.leaf (0))))) (.branch 75 (.branch 74 (.leaf (2)) (.leaf (8))) (.branch 76 (.leaf (5)) (.branch 77 (.leaf (6)) (.leaf (3)))))))))
  code := certificateP9_4182
  counts := ![(.branch 34 (.branch 14 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 53 (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))) (.branch 65 (.branch 60 (.leaf (9)) (.leaf (10))) (.branch 73 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 56 (.branch 41 (.leaf (5)) (.branch 48 (.leaf (6)) (.leaf (7)))) (.branch 64 (.leaf (8)) (.branch 72 (.leaf (9)) (.leaf (10)))))),
  (.branch 35 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 58 (.branch 43 (.leaf (5)) (.branch 51 (.leaf (6)) (.leaf (7)))) (.branch 66 (.leaf (8)) (.branch 74 (.leaf (9)) (.leaf (10)))))),
  (.branch 39 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))) (.branch 62 (.branch 47 (.leaf (5)) (.branch 54 (.leaf (6)) (.leaf (7)))) (.branch 70 (.leaf (8)) (.branch 78 (.leaf (9)) (.leaf (10)))))),
  (.branch 37 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 55 (.branch 45 (.leaf (5)) (.leaf (6))) (.branch 63 (.leaf (7)) (.branch 71 (.leaf (8)) (.leaf (9)))))),
  (.branch 42 (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))) (.branch 59 (.branch 50 (.leaf (5)) (.leaf (6))) (.branch 67 (.leaf (7)) (.branch 76 (.leaf (8)) (.leaf (9)))))),
  (.branch 38 (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 57 (.branch 49 (.leaf (4)) (.leaf (5))) (.branch 68 (.leaf (6)) (.branch 77 (.leaf (7)) (.leaf (8)))))),
  (.branch 36 (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 69 (.leaf (4)) (.leaf (5))))),
  (.branch 44 (.branch 13 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 61 (.leaf (3)) (.branch 75 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 26 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (-6)) (.leaf (-7)))) (.branch 46 (.leaf (-9)) (.branch 65 (.leaf (-10)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-29)) (.leaf (-33)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-22)))),
  (.branch 15 (.leaf (0)) (.leaf (-3))),
  (.branch 28 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))) (.branch 45 (.leaf (-8)) (.branch 71 (.leaf (-9)) (.leaf (-10))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.leaf (-3))) (.branch 67 (.leaf (-4)) (.leaf (-5)))),
  (.branch 18 (.leaf (0)) (.branch 57 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 36 (.leaf (-11)) (.leaf (-12)))),
  (.branch 44 (.branch 13 (.leaf (0)) (.leaf (-3))) (.branch 75 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 75 (.branch 66 (.leaf (-12)) (.branch 74 (.leaf (-11)) (.leaf (-10)))) (.branch 76 (.leaf (-9)) (.branch 77 (.leaf (-8)) (.leaf (-7))))),
  (.branch 73 (.branch 57 (.branch 49 (.leaf (-33)) (.leaf (-32))) (.branch 65 (.leaf (-31)) (.leaf (-30)))) (.branch 75 (.branch 74 (.leaf (-25)) (.leaf (-20))) (.branch 76 (.leaf (-15)) (.branch 77 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 75 (.branch 59 (.leaf (-22)) (.branch 67 (.leaf (-21)) (.leaf (-20)))) (.branch 76 (.leaf (-15)) (.branch 77 (.leaf (-10)) (.leaf (-5))))),
  (.branch 63 (.branch 55 (.leaf (-3)) (.leaf (-2))) (.branch 71 (.leaf (-1)) (.leaf (0)))),
  (.branch 74 (.branch 72 (.leaf (-10)) (.branch 73 (.leaf (-9)) (.leaf (-8)))) (.branch 76 (.branch 75 (.leaf (-7)) (.leaf (-6))) (.branch 77 (.leaf (-5)) (.leaf (-4))))),
  (.branch 77 (.leaf (-5)) (.leaf (-4))),
  (.leaf (-3)),
  (.branch 73 (.branch 70 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 71 (.leaf (-10)) (.branch 72 (.leaf (-9)) (.leaf (-8))))) (.branch 75 (.branch 74 (.leaf (-7)) (.leaf (-6))) (.branch 76 (.leaf (-5)) (.branch 77 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 76 (.leaf (-5)) (.branch 77 (.leaf (-4)) (.leaf (-3))))]
def witnessP9_271_4183 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (3))) (.branch 12 (.leaf (8)) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (3)) (.leaf (6))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (7))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (5)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (3)) (.leaf (0))) (.branch 32 (.leaf (6)) (.branch 33 (.leaf (2)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (4))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (8)) (.leaf (0)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (5)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (6)) (.leaf (0))) (.branch 46 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (1)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (5)) (.branch 52 (.leaf (7)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (6))) (.branch 56 (.leaf (3)) (.branch 57 (.leaf (0)) (.leaf (4))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (2)) (.leaf (1))) (.branch 61 (.leaf (0)) (.branch 62 (.leaf (5)) (.leaf (3))))) (.branch 65 (.branch 64 (.leaf (8)) (.leaf (0))) (.branch 66 (.leaf (6)) (.branch 67 (.leaf (1)) (.leaf (2)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (0)) (.leaf (4))) (.branch 71 (.leaf (0)) (.branch 72 (.leaf (3)) (.leaf (5))))) (.branch 75 (.branch 74 (.leaf (1)) (.leaf (0))) (.branch 76 (.leaf (2)) (.branch 77 (.leaf (6)) (.leaf (7)))))))))
  code := certificateP9_4183
  counts := ![(.branch 39 (.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))) (.branch 57 (.branch 45 (.branch 43 (.leaf (11)) (.leaf (12))) (.branch 49 (.leaf (13)) (.branch 53 (.leaf (14)) (.leaf (15))))) (.branch 69 (.branch 61 (.leaf (16)) (.branch 65 (.leaf (17)) (.leaf (18)))) (.branch 71 (.leaf (19)) (.branch 75 (.leaf (20)) (.leaf (21))))))),
  (.branch 34 (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 54 (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))) (.branch 67 (.branch 60 (.leaf (9)) (.leaf (10))) (.branch 74 (.leaf (11)) (.leaf (12)))))),
  (.branch 42 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))) (.branch 59 (.branch 50 (.leaf (5)) (.leaf (6))) (.branch 68 (.leaf (7)) (.branch 76 (.leaf (8)) (.leaf (9)))))),
  (.branch 37 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))) (.branch 56 (.branch 46 (.leaf (5)) (.leaf (6))) (.branch 63 (.leaf (7)) (.branch 72 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 58 (.branch 47 (.leaf (4)) (.leaf (5))) (.branch 70 (.leaf (6)) (.leaf (7))))),
  (.branch 40 (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 62 (.branch 51 (.leaf (4)) (.leaf (5))) (.branch 73 (.leaf (6)) (.leaf (7))))),
  (.branch 44 (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))) (.branch 66 (.branch 55 (.leaf (4)) (.leaf (5))) (.branch 77 (.leaf (6)) (.leaf (7))))),
  (.branch 52 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 78 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 19 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 45 (.leaf (-24)) (.branch 71 (.leaf (-29)) (.leaf (-34))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 37 (.leaf (-7)) (.branch 63 (.leaf (-8)) (.leaf (-9))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-57)) (.leaf (-58)))) (.branch 47 (.branch 36 (.leaf (-59)) (.leaf (-60))) (.branch 58 (.leaf (-61)) (.leaf (-62))))),
  (.branch 6 (.leaf (0)) (.leaf (-36))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (-8))) (.branch 32 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 76 (.branch 72 (.leaf (-34)) (.leaf (-33))) (.branch 77 (.leaf (-27)) (.leaf (-21)))),
  (.branch 75 (.branch 61 (.leaf (-10)) (.branch 68 (.leaf (-9)) (.leaf (-8)))) (.branch 76 (.leaf (-6)) (.branch 77 (.leaf (-4)) (.leaf (-2))))),
  (.branch 77 (.leaf (-6)) (.leaf (-3))),
  (.branch 75 (.branch 73 (.leaf (-9)) (.branch 74 (.leaf (-8)) (.leaf (-7)))) (.branch 76 (.leaf (-6)) (.branch 77 (.leaf (-5)) (.leaf (-4))))),
  (.branch 73 (.branch 71 (.branch 59 (.leaf (-62)) (.leaf (-56))) (.branch 72 (.leaf (-49)) (.leaf (-42)))) (.branch 75 (.branch 74 (.leaf (-35)) (.leaf (-28))) (.branch 76 (.leaf (-21)) (.branch 77 (.leaf (-14)) (.leaf (-7)))))),
  (.branch 75 (.branch 7 (.leaf (-36)) (.branch 74 (.leaf (-35)) (.leaf (-28)))) (.branch 76 (.leaf (-21)) (.branch 77 (.leaf (-14)) (.leaf (-7))))),
  (.branch 33 (.leaf (-10)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 71 (.branch 67 (.branch 65 (.leaf (-14)) (.branch 66 (.leaf (-13)) (.leaf (-12)))) (.branch 69 (.branch 68 (.leaf (-11)) (.leaf (-10))) (.branch 70 (.leaf (-9)) (.leaf (-8))))) (.branch 74 (.branch 72 (.leaf (-7)) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_271_4184 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (7)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (6))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (8)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (5))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (3)) (.leaf (7))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (1))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (3)) (.leaf (8)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (5))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (1)) (.leaf (4))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (3))) (.branch 37 (.leaf (7)) (.branch 38 (.leaf (6)) (.leaf (2)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (4)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (5))) (.branch 46 (.leaf (8)) (.branch 47 (.leaf (2)) (.leaf (0)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (6))) (.branch 51 (.leaf (3)) (.branch 52 (.leaf (0)) (.leaf (4))))) (.branch 55 (.branch 54 (.leaf (7)) (.leaf (2))) (.branch 56 (.leaf (0)) (.branch 57 (.leaf (1)) (.leaf (5))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (3)) (.leaf (8))) (.branch 61 (.leaf (0)) (.branch 62 (.leaf (4)) (.leaf (2))))) (.branch 65 (.branch 64 (.leaf (6)) (.leaf (1))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (3)) (.leaf (7)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (0)) (.leaf (5))) (.branch 71 (.leaf (2)) (.branch 72 (.leaf (1)) (.leaf (4))))) (.branch 75 (.branch 74 (.leaf (0)) (.leaf (3))) (.branch 76 (.leaf (8)) (.branch 77 (.leaf (6)) (.leaf (2)))))))))
  code := certificateP9_4184
  counts := ![(.branch 35 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))) (.branch 56 (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.branch 52 (.leaf (12)) (.leaf (13))))) (.branch 66 (.branch 61 (.leaf (14)) (.leaf (15))) (.branch 69 (.leaf (16)) (.branch 74 (.leaf (17)) (.leaf (18))))))),
  (.branch 33 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 57 (.branch 41 (.leaf (5)) (.branch 49 (.leaf (6)) (.leaf (7)))) (.branch 65 (.leaf (8)) (.branch 72 (.leaf (9)) (.leaf (10)))))),
  (.branch 39 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))) (.branch 63 (.branch 47 (.leaf (5)) (.branch 55 (.leaf (6)) (.leaf (7)))) (.branch 71 (.leaf (8)) (.branch 78 (.leaf (9)) (.leaf (10)))))),
  (.branch 36 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 59 (.branch 43 (.leaf (5)) (.branch 51 (.leaf (6)) (.leaf (7)))) (.branch 67 (.leaf (8)) (.branch 75 (.leaf (9)) (.leaf (10)))))),
  (.branch 34 (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.branch 73 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 58 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 70 (.leaf (5)) (.leaf (6))))),
  (.branch 38 (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 64 (.branch 50 (.leaf (3)) (.leaf (4))) (.branch 77 (.leaf (5)) (.leaf (6))))),
  (.branch 37 (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 54 (.leaf (3)) (.branch 68 (.leaf (4)) (.leaf (5))))),
  (.branch 46 (.branch 15 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 60 (.leaf (3)) (.branch 76 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 9 (.leaf (-8)) (.branch 13 (.leaf (-9)) (.leaf (-10))))) (.branch 52 (.branch 30 (.leaf (-11)) (.leaf (-12))) (.branch 56 (.leaf (-13)) (.branch 69 (.leaf (-14)) (.leaf (-15)))))),
  (.branch 2 (.leaf (0)) (.branch 33 (.leaf (-29)) (.leaf (-30)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 3 (.leaf (0)) (.branch 42 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 31 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (-9))) (.branch 68 (.leaf (-11)) (.leaf (-12)))),
  (.branch 29 (.branch 15 (.leaf (0)) (.leaf (-1))) (.branch 60 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 75 (.branch 70 (.leaf (-15)) (.leaf (-14))) (.branch 76 (.leaf (-12)) (.branch 77 (.leaf (-10)) (.leaf (-8))))),
  (.branch 75 (.branch 73 (.leaf (-30)) (.branch 74 (.leaf (-25)) (.leaf (-20)))) (.branch 76 (.leaf (-15)) (.branch 77 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 60 (.branch 44 (.leaf (-19)) (.branch 52 (.leaf (-18)) (.leaf (-17)))) (.branch 76 (.branch 68 (.leaf (-16)) (.leaf (-15))) (.branch 77 (.leaf (-10)) (.leaf (-5))))),
  (.branch 75 (.branch 63 (.leaf (-8)) (.branch 74 (.leaf (-7)) (.leaf (-6)))) (.branch 76 (.leaf (-5)) (.branch 77 (.leaf (-4)) (.leaf (-3))))),
  (.branch 74 (.branch 72 (.branch 71 (.leaf (-8)) (.leaf (-7))) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 73 (.branch 70 (.branch 69 (.leaf (-12)) (.leaf (-11))) (.branch 71 (.leaf (-10)) (.branch 72 (.leaf (-9)) (.leaf (-8))))) (.branch 75 (.branch 74 (.leaf (-7)) (.leaf (-6))) (.branch 76 (.leaf (-5)) (.branch 77 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 77 (.leaf (-4)) (.leaf (-3)))]
def witnessP9_271_4185 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (7)) (.branch 13 (.leaf (1)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (6)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (4))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (5)) (.branch 23 (.leaf (3)) (.leaf (1))))) (.branch 26 (.branch 25 (.leaf (8)) (.leaf (0))) (.branch 27 (.leaf (4)) (.branch 28 (.leaf (2)) (.leaf (1)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (3))) (.branch 32 (.leaf (6)) (.branch 33 (.leaf (2)) (.leaf (4))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (7)) (.leaf (2)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (4)) (.leaf (5)))) (.branch 45 (.branch 44 (.leaf (3)) (.leaf (0))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (1)) (.leaf (3)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (4))) (.branch 51 (.leaf (8)) (.branch 52 (.leaf (1)) (.leaf (2))))) (.branch 55 (.branch 54 (.leaf (6)) (.leaf (0))) (.branch 56 (.leaf (3)) (.branch 57 (.leaf (1)) (.leaf (4))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (0)) (.leaf (2))) (.branch 61 (.leaf (5)) (.branch 62 (.leaf (3)) (.leaf (1))))) (.branch 65 (.branch 64 (.leaf (7)) (.leaf (0))) (.branch 66 (.leaf (4)) (.branch 67 (.leaf (2)) (.leaf (1)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (0)) (.leaf (3))) (.branch 71 (.leaf (6)) (.branch 72 (.leaf (2)) (.leaf (4))))) (.branch 75 (.branch 74 (.leaf (1)) (.leaf (0))) (.branch 76 (.leaf (3)) (.branch 77 (.leaf (8)) (.leaf (2)))))))))
  code := certificateP9_4185
  counts := ![(.branch 36 (.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))) (.branch 55 (.branch 45 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 49 (.leaf (10)) (.leaf (11)))) (.branch 65 (.branch 59 (.leaf (12)) (.leaf (13))) (.branch 69 (.leaf (14)) (.branch 75 (.leaf (15)) (.leaf (16))))))),
  (.branch 35 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))) (.branch 57 (.branch 47 (.branch 41 (.leaf (7)) (.leaf (8))) (.branch 52 (.leaf (9)) (.leaf (10)))) (.branch 68 (.branch 63 (.leaf (11)) (.leaf (12))) (.branch 74 (.leaf (13)) (.leaf (14)))))),
  (.branch 39 (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))) (.branch 60 (.branch 46 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))) (.branch 72 (.branch 67 (.leaf (9)) (.leaf (10))) (.branch 78 (.leaf (11)) (.leaf (12)))))),
  (.branch 37 (.branch 17 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))) (.branch 56 (.branch 44 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))) (.branch 70 (.branch 62 (.leaf (9)) (.leaf (10))) (.branch 76 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 58 (.branch 42 (.leaf (5)) (.branch 50 (.leaf (6)) (.leaf (7)))) (.branch 66 (.leaf (8)) (.branch 73 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.branch 71 (.leaf (3)) (.leaf (4))))),
  (.branch 38 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3)))),
  (.branch 51 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 77 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 49 (.leaf (-5)) (.leaf (-6)))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))) (.branch 57 (.branch 29 (.leaf (-14)) (.leaf (-15))) (.branch 68 (.leaf (-16)) (.leaf (-17))))),
  (.branch 39 (.branch 33 (.leaf (0)) (.leaf (-3))) (.branch 72 (.leaf (-6)) (.leaf (-9)))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 48 (.leaf (-5)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 34 (.leaf (-24)) (.leaf (-25)))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (-16))) (.branch 61 (.leaf (-18)) (.leaf (-19)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (-6))) (.branch 71 (.leaf (-10)) (.leaf (-13)))),
  (.branch 12 (.leaf (0)) (.leaf (-14))),
  (.branch 25 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 76 (.branch 70 (.leaf (-6)) (.leaf (-5))) (.branch 77 (.leaf (-4)) (.leaf (-3)))),
  (.branch 75 (.branch 69 (.leaf (-17)) (.leaf (-16))) (.branch 76 (.leaf (-13)) (.branch 77 (.leaf (-10)) (.leaf (-7))))),
  (.branch 74 (.branch 73 (.leaf (-9)) (.leaf (-5))) (.branch 75 (.leaf (-1)) (.leaf (0)))),
  (.branch 77 (.leaf (-8)) (.leaf (-7))),
  (.branch 75 (.branch 74 (.leaf (-25)) (.leaf (-20))) (.branch 76 (.leaf (-15)) (.branch 77 (.leaf (-10)) (.leaf (-5))))),
  (.branch 69 (.branch 65 (.branch 63 (.branch 62 (.leaf (-19)) (.leaf (-18))) (.branch 64 (.leaf (-17)) (.leaf (-16)))) (.branch 67 (.branch 66 (.leaf (-15)) (.leaf (-14))) (.branch 68 (.leaf (-13)) (.leaf (-12))))) (.branch 73 (.branch 71 (.branch 70 (.leaf (-11)) (.leaf (-10))) (.branch 72 (.leaf (-9)) (.leaf (-8)))) (.branch 75 (.branch 74 (.leaf (-7)) (.leaf (-6))) (.branch 76 (.leaf (-5)) (.branch 77 (.leaf (-4)) (.leaf (-3))))))),
  (.branch 74 (.branch 72 (.leaf (-13)) (.branch 73 (.leaf (-12)) (.leaf (-11)))) (.branch 76 (.branch 75 (.leaf (-10)) (.leaf (-9))) (.branch 77 (.leaf (-8)) (.leaf (-7))))),
  (.branch 71 (.branch 67 (.branch 65 (.leaf (-14)) (.branch 66 (.leaf (-13)) (.leaf (-12)))) (.branch 69 (.branch 68 (.leaf (-11)) (.leaf (-10))) (.branch 70 (.leaf (-9)) (.leaf (-8))))) (.branch 74 (.branch 72 (.leaf (-7)) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_271_4186 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (4))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (5)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (8))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (5)) (.leaf (1))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (4))) (.branch 27 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (0)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (3)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (7)) (.leaf (4))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (5))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (3)) (.leaf (2)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (4)) (.leaf (5)))) (.branch 45 (.branch 44 (.leaf (8)) (.leaf (0))) (.branch 46 (.leaf (3)) (.branch 47 (.leaf (2)) (.leaf (1)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (6)) (.leaf (4))) (.branch 51 (.leaf (0)) (.branch 52 (.leaf (5)) (.leaf (1))))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (2))) (.branch 56 (.leaf (0)) (.branch 57 (.leaf (4)) (.leaf (7))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (5)) (.leaf (1))) (.branch 61 (.leaf (3)) (.branch 62 (.leaf (0)) (.leaf (2))))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (4))) (.branch 66 (.leaf (5)) (.branch 67 (.leaf (6)) (.leaf (0)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (3)) (.leaf (2))) (.branch 71 (.leaf (1)) (.branch 72 (.leaf (8)) (.leaf (4))))) (.branch 75 (.branch 74 (.leaf (0)) (.leaf (5))) (.branch 76 (.leaf (1)) (.branch 77 (.leaf (3)) (.leaf (2)))))))))
  code := certificateP9_4186
  counts := ![(.branch 35 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))) (.branch 56 (.branch 45 (.branch 40 (.leaf (7)) (.leaf (8))) (.branch 51 (.leaf (9)) (.leaf (10)))) (.branch 68 (.branch 62 (.leaf (11)) (.leaf (12))) (.branch 74 (.leaf (13)) (.leaf (14)))))),
  (.branch 37 (.branch 14 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))) (.branch 60 (.branch 48 (.branch 41 (.leaf (7)) (.leaf (8))) (.branch 53 (.leaf (9)) (.leaf (10)))) (.branch 71 (.branch 64 (.leaf (11)) (.leaf (12))) (.branch 76 (.leaf (13)) (.leaf (14)))))),
  (.branch 39 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))) (.branch 63 (.branch 47 (.leaf (5)) (.branch 55 (.leaf (6)) (.leaf (7)))) (.branch 70 (.leaf (8)) (.branch 78 (.leaf (9)) (.leaf (10)))))),
  (.branch 38 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))) (.branch 61 (.branch 46 (.leaf (5)) (.branch 54 (.leaf (6)) (.leaf (7)))) (.branch 69 (.leaf (8)) (.branch 77 (.leaf (9)) (.leaf (10)))))),
  (.branch 34 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 57 (.branch 42 (.leaf (5)) (.branch 50 (.leaf (6)) (.leaf (7)))) (.branch 65 (.leaf (8)) (.branch 73 (.leaf (9)) (.leaf (10)))))),
  (.branch 36 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 59 (.branch 43 (.leaf (5)) (.branch 52 (.leaf (6)) (.leaf (7)))) (.branch 66 (.leaf (8)) (.branch 75 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.branch 67 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 72 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (-14)) (.leaf (-16)))) (.branch 45 (.leaf (-17)) (.branch 56 (.leaf (-18)) (.leaf (-19))))),
  (.branch 25 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 41 (.leaf (-5)) (.branch 64 (.leaf (-7)) (.leaf (-8))))),
  (.branch 31 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (-4)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-24)) (.leaf (-27)))),
  (.branch 27 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 66 (.leaf (-5)) (.leaf (-6)))),
  (.branch 28 (.branch 10 (.leaf (0)) (.leaf (-10))) (.branch 67 (.leaf (-12)) (.leaf (-13)))),
  (.branch 5 (.leaf (0)) (.branch 58 (.leaf (-22)) (.leaf (-23)))),
  (.branch 19 (.leaf (0)) (.branch 44 (.leaf (-8)) (.leaf (-10))))]
  high := ![(.branch 69 (.branch 57 (.leaf (-19)) (.branch 63 (.leaf (-18)) (.leaf (-17)))) (.branch 76 (.branch 75 (.leaf (-16)) (.leaf (-13))) (.branch 77 (.leaf (-10)) (.leaf (-7))))),
  (.branch 77 (.leaf (-8)) (.leaf (-7))),
  (.branch 71 (.leaf (-1)) (.leaf (0))),
  (.branch 62 (.leaf (-7)) (.branch 70 (.leaf (-6)) (.leaf (-5)))),
  (.branch 74 (.branch 58 (.leaf (-27)) (.branch 66 (.leaf (-26)) (.leaf (-25)))) (.branch 76 (.branch 75 (.leaf (-20)) (.leaf (-15))) (.branch 77 (.leaf (-10)) (.leaf (-5))))),
  (.branch 76 (.branch 67 (.leaf (-6)) (.leaf (-5))) (.branch 77 (.leaf (-4)) (.leaf (-3)))),
  (.branch 72 (.branch 69 (.branch 68 (.leaf (-13)) (.leaf (-12))) (.branch 70 (.leaf (-11)) (.branch 71 (.leaf (-10)) (.leaf (-9))))) (.branch 75 (.branch 73 (.leaf (-8)) (.branch 74 (.leaf (-7)) (.leaf (-6)))) (.branch 76 (.leaf (-5)) (.branch 77 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (-23)) (.leaf (-22))) (.branch 61 (.leaf (-21)) (.branch 62 (.leaf (-20)) (.leaf (-19))))) (.branch 65 (.branch 64 (.leaf (-18)) (.leaf (-17))) (.branch 66 (.leaf (-16)) (.branch 67 (.leaf (-15)) (.leaf (-14)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (-13)) (.leaf (-12))) (.branch 71 (.leaf (-11)) (.branch 72 (.leaf (-10)) (.leaf (-9))))) (.branch 75 (.branch 74 (.leaf (-8)) (.leaf (-7))) (.branch 76 (.leaf (-6)) (.branch 77 (.leaf (-5)) (.leaf (-4))))))),
  (.branch 74 (.branch 45 (.leaf (-10)) (.branch 73 (.leaf (-9)) (.leaf (-8)))) (.branch 76 (.branch 75 (.leaf (-7)) (.leaf (-6))) (.branch 77 (.leaf (-5)) (.leaf (-4)))))]
def witnessP9_271_4187 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (7)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (8)) (.leaf (4))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (2))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (6)) (.leaf (5))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 26 (.branch 25 (.leaf (7)) (.leaf (2))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (4)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (8)) (.leaf (0))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (1)) (.leaf (5))))) (.branch 36 (.branch 35 (.leaf (6)) (.leaf (0))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (1)) (.leaf (2)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (7))) (.branch 42 (.leaf (4)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (2))) (.branch 46 (.leaf (8)) (.branch 47 (.leaf (5)) (.leaf (1)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (6)) (.branch 52 (.leaf (2)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (4))) (.branch 56 (.leaf (7)) (.branch 57 (.leaf (0)) (.leaf (2))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (1)) (.leaf (5))) (.branch 61 (.leaf (8)) (.branch 62 (.leaf (0)) (.leaf (3))))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (2))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (6)) (.leaf (4)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (1)) (.leaf (0))) (.branch 71 (.leaf (2)) (.branch 72 (.leaf (7)) (.leaf (5))))) (.branch 75 (.branch 74 (.leaf (1)) (.leaf (0))) (.branch 76 (.leaf (3)) (.branch 77 (.leaf (8)) (.leaf (2)))))))))
  code := certificateP9_4187
  counts := ![(.branch 36 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))) (.branch 57 (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.branch 53 (.leaf (12)) (.leaf (13))))) (.branch 66 (.branch 62 (.leaf (14)) (.leaf (15))) (.branch 70 (.leaf (16)) (.branch 75 (.leaf (17)) (.leaf (18))))))),
  (.branch 38 (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))) (.branch 59 (.branch 48 (.branch 43 (.leaf (8)) (.leaf (9))) (.branch 54 (.leaf (10)) (.leaf (11)))) (.branch 69 (.branch 64 (.leaf (12)) (.leaf (13))) (.branch 74 (.leaf (14)) (.leaf (15)))))),
  (.branch 39 (.branch 19 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))) (.branch 58 (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))) (.branch 71 (.branch 65 (.leaf (9)) (.leaf (10))) (.branch 78 (.leaf (11)) (.leaf (12)))))),
  (.branch 37 (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 63 (.branch 50 (.leaf (3)) (.leaf (4))) (.branch 76 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 34 (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 60 (.branch 47 (.leaf (3)) (.leaf (4))) (.branch 73 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 4 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 67 (.leaf (4)) (.leaf (5))))),
  (.branch 41 (.branch 9 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 56 (.leaf (3)) (.branch 72 (.leaf (4)) (.leaf (5))))),
  (.branch 46 (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 61 (.leaf (3)) (.branch 77 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 17 (.leaf (-18)) (.branch 22 (.leaf (-19)) (.leaf (-20))))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 35 (.leaf (-58)) (.leaf (-59)))),
  (.branch 9 (.leaf (0)) (.leaf (-33))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (-3))) (.branch 61 (.leaf (-6)) (.leaf (-7))))]
  high := ![(.branch 76 (.branch 71 (.leaf (-11)) (.leaf (-9))) (.branch 77 (.leaf (-6)) (.leaf (-3)))),
  (.branch 76 (.branch 75 (.leaf (-20)) (.leaf (-15))) (.branch 77 (.leaf (-10)) (.leaf (-5)))),
  (.branch 72 (.leaf (-1)) (.leaf (0))),
  (.branch 77 (.leaf (-2)) (.leaf (-1))),
  (.branch 73 (.branch 70 (.branch 69 (.leaf (-10)) (.leaf (-9))) (.branch 71 (.leaf (-8)) (.branch 72 (.leaf (-7)) (.leaf (-6))))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.branch 71 (.branch 68 (.branch 36 (.leaf (-59)) (.branch 52 (.leaf (-57)) (.leaf (-55)))) (.branch 69 (.leaf (-50)) (.branch 70 (.leaf (-45)) (.leaf (-40))))) (.branch 74 (.branch 72 (.leaf (-35)) (.branch 73 (.leaf (-30)) (.leaf (-25)))) (.branch 76 (.branch 75 (.leaf (-20)) (.leaf (-15))) (.branch 77 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 74 (.branch 57 (.branch 10 (.leaf (-33)) (.leaf (-32))) (.branch 73 (.leaf (-30)) (.leaf (-25)))) (.branch 76 (.branch 75 (.leaf (-20)) (.leaf (-15))) (.branch 77 (.leaf (-10)) (.leaf (-5))))),
  (.branch 62 (.leaf (-7)) (.leaf (-5)))]
def witnessP9_271_4188 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (7)) (.branch 8 (.leaf (3)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (2)) (.leaf (6))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (0))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (5)) (.leaf (4))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (8)) (.leaf (0))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (6))))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (4)) (.branch 28 (.leaf (5)) (.leaf (2)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (3)) (.leaf (0))) (.branch 32 (.leaf (7)) (.branch 33 (.leaf (1)) (.leaf (6))))) (.branch 36 (.branch 35 (.leaf (4)) (.leaf (0))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (5)) (.leaf (3)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (4)) (.leaf (6)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (0))) (.branch 46 (.leaf (8)) (.branch 47 (.leaf (3)) (.leaf (5)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (4)) (.branch 52 (.leaf (2)) (.leaf (6))))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (0))) (.branch 56 (.leaf (1)) (.branch 57 (.leaf (5)) (.leaf (4))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (7)) (.leaf (0))) (.branch 61 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (6))))) (.branch 65 (.branch 64 (.leaf (1)) (.leaf (0))) (.branch 66 (.leaf (4)) (.branch 67 (.leaf (5)) (.leaf (2)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (3)) (.leaf (0))) (.branch 71 (.leaf (8)) (.branch 72 (.leaf (1)) (.leaf (6))))) (.branch 75 (.branch 74 (.leaf (4)) (.leaf (0))) (.branch 76 (.leaf (2)) (.branch 77 (.leaf (5)) (.leaf (3)))))))))
  code := certificateP9_4188
  counts := ![(.branch 36 (.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))) (.branch 55 (.branch 45 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 50 (.leaf (10)) (.leaf (11)))) (.branch 65 (.branch 60 (.leaf (12)) (.leaf (13))) (.branch 70 (.leaf (14)) (.branch 75 (.leaf (15)) (.leaf (16))))))),
  (.branch 33 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 56 (.branch 41 (.leaf (5)) (.branch 49 (.leaf (6)) (.leaf (7)))) (.branch 64 (.leaf (8)) (.branch 72 (.leaf (9)) (.leaf (10)))))),
  (.branch 37 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 61 (.branch 44 (.leaf (5)) (.branch 52 (.leaf (6)) (.leaf (7)))) (.branch 68 (.leaf (8)) (.branch 76 (.leaf (9)) (.leaf (10)))))),
  (.branch 39 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))) (.branch 62 (.branch 47 (.leaf (5)) (.branch 54 (.leaf (6)) (.leaf (7)))) (.branch 69 (.leaf (8)) (.branch 78 (.leaf (9)) (.leaf (10)))))),
  (.branch 35 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 58 (.branch 42 (.leaf (5)) (.branch 51 (.leaf (6)) (.leaf (7)))) (.branch 66 (.leaf (8)) (.branch 74 (.leaf (9)) (.leaf (10)))))),
  (.branch 38 (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 57 (.branch 48 (.leaf (4)) (.leaf (5))) (.branch 67 (.leaf (6)) (.branch 77 (.leaf (7)) (.leaf (8)))))),
  (.branch 34 (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.branch 73 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 46 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 71 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-31))),
  (.branch 2 (.leaf (0)) (.branch 17 (.leaf (-29)) (.leaf (-32)))),
  (.branch 5 (.leaf (0)) (.branch 44 (.leaf (-3)) (.leaf (-4)))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (-1))) (.branch 69 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 42 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-3)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-23))),
  (.branch 7 (.leaf (0)) (.branch 32 (.leaf (-19)) (.leaf (-20)))),
  (.branch 20 (.leaf (0)) (.branch 71 (.leaf (-6)) (.leaf (-7))))]
  high := ![(.branch 61 (.branch 46 (.branch 41 (.leaf (-31)) (.leaf (-30))) (.branch 51 (.leaf (-29)) (.branch 56 (.leaf (-28)) (.leaf (-27))))) (.branch 71 (.branch 66 (.leaf (-26)) (.leaf (-25))) (.branch 76 (.leaf (-24)) (.branch 77 (.leaf (-16)) (.leaf (-8)))))),
  (.branch 74 (.branch 65 (.branch 57 (.leaf (-32)) (.leaf (-31))) (.branch 73 (.leaf (-30)) (.leaf (-25)))) (.branch 76 (.branch 75 (.leaf (-20)) (.leaf (-15))) (.branch 77 (.leaf (-10)) (.leaf (-5))))),
  (.branch 77 (.leaf (-4)) (.leaf (-3))),
  (.branch 71 (.branch 70 (.leaf (-3)) (.leaf (-2))) (.branch 72 (.leaf (-1)) (.leaf (0)))),
  (.branch 76 (.branch 75 (.leaf (-6)) (.leaf (-5))) (.branch 77 (.leaf (-4)) (.leaf (-3)))),
  (.branch 58 (.leaf (-6)) (.branch 68 (.leaf (-5)) (.leaf (-4)))),
  (.branch 74 (.branch 54 (.branch 44 (.leaf (-23)) (.leaf (-22))) (.branch 64 (.leaf (-21)) (.leaf (-20)))) (.branch 76 (.branch 75 (.leaf (-16)) (.leaf (-12))) (.branch 77 (.leaf (-8)) (.leaf (-4))))),
  (.branch 68 (.branch 63 (.branch 60 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 61 (.leaf (-18)) (.branch 62 (.leaf (-17)) (.leaf (-16))))) (.branch 65 (.branch 64 (.leaf (-15)) (.leaf (-14))) (.branch 66 (.leaf (-13)) (.branch 67 (.leaf (-12)) (.leaf (-11)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (-10)) (.leaf (-9))) (.branch 71 (.leaf (-8)) (.branch 72 (.leaf (-7)) (.leaf (-6))))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 74 (.branch 72 (.leaf (-7)) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_271_4189 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (3)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (0))) (.branch 17 (.leaf (8)) (.branch 18 (.leaf (2)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (6))) (.branch 22 (.leaf (5)) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (0)) (.leaf (4)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (7)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (6)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (5)) (.leaf (0))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (1)) (.leaf (3)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (4)) (.leaf (8)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (6))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (2)) (.leaf (0)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (5)) (.leaf (1))) (.branch 51 (.leaf (0)) (.branch 52 (.leaf (3)) (.leaf (1))))) (.branch 55 (.branch 54 (.leaf (4)) (.leaf (0))) (.branch 56 (.leaf (7)) (.branch 57 (.leaf (2)) (.leaf (1))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (0)) (.leaf (6))) (.branch 61 (.leaf (5)) (.branch 62 (.leaf (1)) (.leaf (0))))) (.branch 65 (.branch 64 (.leaf (3)) (.leaf (1))) (.branch 66 (.leaf (2)) (.branch 67 (.leaf (0)) (.leaf (4)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (8)) (.leaf (1))) (.branch 71 (.leaf (0)) (.branch 72 (.leaf (6)) (.leaf (1))))) (.branch 75 (.branch 74 (.leaf (5)) (.leaf (0))) (.branch 76 (.leaf (2)) (.branch 77 (.leaf (1)) (.leaf (3)))))))))
  code := certificateP9_4189
  counts := ![(.branch 36 (.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 28 (.leaf (7)) (.branch 32 (.leaf (8)) (.leaf (9)))))) (.branch 55 (.branch 44 (.branch 40 (.leaf (10)) (.leaf (11))) (.branch 48 (.leaf (12)) (.branch 51 (.leaf (13)) (.leaf (14))))) (.branch 67 (.branch 59 (.leaf (15)) (.branch 63 (.leaf (16)) (.leaf (17)))) (.branch 71 (.leaf (18)) (.branch 75 (.leaf (19)) (.leaf (20))))))),
  (.branch 38 (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 23 (.leaf (5)) (.leaf (6))) (.branch 31 (.leaf (7)) (.branch 34 (.leaf (8)) (.leaf (9)))))) (.branch 58 (.branch 46 (.branch 41 (.leaf (10)) (.leaf (11))) (.branch 50 (.leaf (12)) (.branch 53 (.leaf (13)) (.leaf (14))))) (.branch 70 (.branch 62 (.leaf (15)) (.branch 65 (.leaf (16)) (.leaf (17)))) (.branch 73 (.leaf (18)) (.branch 77 (.leaf (19)) (.leaf (20))))))),
  (.branch 37 (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 57 (.branch 47 (.leaf (4)) (.leaf (5))) (.branch 66 (.leaf (6)) (.branch 76 (.leaf (7)) (.leaf (8)))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 64 (.branch 52 (.leaf (3)) (.leaf (4))) (.branch 78 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 61 (.branch 49 (.leaf (3)) (.leaf (4))) (.branch 74 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 60 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 72 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 43 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 69 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-29)) (.leaf (-36)))),
  (.branch 2 (.leaf (0)) (.branch 41 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-7)) (.leaf (-9)))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-10)) (.leaf (-11)))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (-3)) (.leaf (-4)))),
  (.branch 33 (.branch 6 (.leaf (0)) (.leaf (-8))) (.branch 45 (.leaf (-9)) (.branch 72 (.leaf (-11)) (.leaf (-12))))),
  (.branch 4 (.leaf (0)) (.leaf (-22))),
  (.branch 17 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 64 (.branch 56 (.branch 52 (.leaf (-36)) (.leaf (-35))) (.branch 60 (.leaf (-34)) (.leaf (-33)))) (.branch 72 (.branch 68 (.leaf (-32)) (.leaf (-31))) (.branch 76 (.leaf (-30)) (.branch 77 (.leaf (-20)) (.leaf (-10)))))),
  (.leaf (-3)),
  (.branch 67 (.leaf (-9)) (.branch 77 (.leaf (-8)) (.leaf (-4)))),
  (.branch 65 (.leaf (-1)) (.leaf (0))),
  (.branch 72 (.branch 69 (.branch 55 (.leaf (-11)) (.leaf (-10))) (.branch 70 (.leaf (-9)) (.branch 71 (.leaf (-8)) (.leaf (-7))))) (.branch 75 (.branch 73 (.leaf (-6)) (.branch 74 (.leaf (-5)) (.leaf (-4)))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1)))),
  (.branch 75 (.branch 73 (.leaf (-12)) (.branch 74 (.leaf (-11)) (.leaf (-10)))) (.branch 76 (.leaf (-9)) (.branch 77 (.leaf (-8)) (.leaf (-7))))),
  (.branch 67 (.branch 61 (.branch 58 (.branch 57 (.leaf (-22)) (.leaf (-21))) (.branch 59 (.leaf (-20)) (.branch 60 (.leaf (-19)) (.leaf (-18))))) (.branch 64 (.branch 62 (.leaf (-17)) (.branch 63 (.leaf (-16)) (.leaf (-15)))) (.branch 65 (.leaf (-14)) (.branch 66 (.leaf (-13)) (.leaf (-12)))))) (.branch 72 (.branch 69 (.branch 68 (.leaf (-11)) (.leaf (-10))) (.branch 70 (.leaf (-9)) (.branch 71 (.leaf (-8)) (.leaf (-7))))) (.branch 75 (.branch 73 (.leaf (-6)) (.branch 74 (.leaf (-5)) (.leaf (-4)))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 73 (.branch 71 (.branch 70 (.leaf (-9)) (.leaf (-8))) (.branch 72 (.leaf (-7)) (.leaf (-6)))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_271_4190 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (8)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (2))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (6)) (.leaf (5))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (7)) (.branch 23 (.leaf (4)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (1)) (.branch 28 (.leaf (5)) (.leaf (8)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (6))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (4)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (3))) (.branch 37 (.leaf (7)) (.branch 38 (.leaf (5)) (.leaf (2)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (4)) (.leaf (8)))) (.branch 45 (.branch 44 (.leaf (6)) (.leaf (0))) (.branch 46 (.leaf (3)) (.branch 47 (.leaf (2)) (.leaf (1)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (5)) (.leaf (0))) (.branch 51 (.leaf (4)) (.branch 52 (.leaf (7)) (.leaf (1))))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (2))) (.branch 56 (.leaf (3)) (.branch 57 (.leaf (6)) (.leaf (5))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (8)) (.branch 62 (.leaf (4)) (.leaf (2))))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (3))) (.branch 66 (.leaf (1)) (.branch 67 (.leaf (5)) (.leaf (7)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (0)) (.leaf (6))) (.branch 71 (.leaf (2)) (.branch 72 (.leaf (4)) (.leaf (1))))) (.branch 75 (.branch 74 (.leaf (0)) (.leaf (3))) (.branch 76 (.leaf (8)) (.branch 77 (.leaf (5)) (.leaf (2)))))))))
  code := certificateP9_4190
  counts := ![(.branch 35 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))) (.branch 54 (.branch 45 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 50 (.leaf (10)) (.leaf (11)))) (.branch 64 (.branch 59 (.leaf (12)) (.leaf (13))) (.branch 69 (.leaf (14)) (.branch 74 (.leaf (15)) (.leaf (16))))))),
  (.branch 34 (.branch 14 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 53 (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))) (.branch 66 (.branch 60 (.leaf (9)) (.leaf (10))) (.branch 73 (.leaf (11)) (.leaf (12)))))),
  (.branch 39 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))) (.branch 63 (.branch 47 (.leaf (5)) (.branch 55 (.leaf (6)) (.leaf (7)))) (.branch 71 (.leaf (8)) (.branch 78 (.leaf (9)) (.leaf (10)))))),
  (.branch 36 (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 65 (.leaf (6)) (.branch 75 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.branch 72 (.leaf (7)) (.leaf (8)))))),
  (.branch 38 (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 58 (.branch 49 (.leaf (4)) (.leaf (5))) (.branch 67 (.leaf (6)) (.branch 77 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 70 (.leaf (5)) (.leaf (6))))),
  (.branch 37 (.branch 4 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 68 (.leaf (4)) (.leaf (5))))),
  (.branch 43 (.branch 13 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 61 (.leaf (3)) (.branch 76 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-31)) (.leaf (-36)))),
  (.branch 27 (.branch 2 (.leaf (0)) (.branch 14 (.leaf (-14)) (.leaf (-18)))) (.branch 53 (.leaf (-19)) (.branch 66 (.leaf (-21)) (.leaf (-22))))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (-11)) (.leaf (-13)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 51 (.leaf (-8)) (.leaf (-9)))),
  (.branch 28 (.branch 19 (.leaf (0)) (.leaf (-1))) (.branch 67 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 37 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 52 (.leaf (-14)) (.branch 68 (.leaf (-16)) (.leaf (-17))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (-4))) (.branch 43 (.leaf (-5)) (.branch 76 (.leaf (-8)) (.leaf (-9)))))]
  high := ![(.branch 70 (.branch 60 (.branch 55 (.leaf (-36)) (.leaf (-35))) (.branch 65 (.leaf (-34)) (.leaf (-33)))) (.branch 76 (.branch 75 (.leaf (-32)) (.leaf (-24))) (.branch 77 (.leaf (-16)) (.leaf (-8))))),
  (.branch 75 (.branch 67 (.leaf (-22)) (.branch 74 (.leaf (-21)) (.leaf (-18)))) (.branch 76 (.leaf (-15)) (.branch 77 (.leaf (-12)) (.leaf (-9))))),
  (.leaf (0)),
  (.branch 76 (.branch 66 (.leaf (-13)) (.leaf (-12))) (.branch 77 (.leaf (-8)) (.leaf (-4)))),
  (.branch 74 (.branch 52 (.leaf (-9)) (.branch 73 (.leaf (-8)) (.leaf (-7)))) (.branch 76 (.branch 75 (.leaf (-6)) (.leaf (-5))) (.branch 77 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 74 (.branch 72 (.branch 71 (.leaf (-8)) (.leaf (-7))) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.branch 73 (.branch 70 (.branch 69 (.leaf (-17)) (.leaf (-16))) (.branch 71 (.leaf (-15)) (.branch 72 (.leaf (-14)) (.leaf (-13))))) (.branch 75 (.branch 74 (.leaf (-12)) (.leaf (-11))) (.branch 76 (.leaf (-10)) (.branch 77 (.leaf (-9)) (.leaf (-8)))))),
  (.branch 77 (.leaf (-9)) (.leaf (-8)))]
def witnessP9_271_4191 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (8)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (7))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (4)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (5))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (8)) (.leaf (2))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (6)) (.branch 23 (.leaf (4)) (.leaf (7))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (5)) (.branch 28 (.leaf (1)) (.leaf (2)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (8))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (6)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (3))) (.branch 37 (.leaf (7)) (.branch 38 (.leaf (2)) (.leaf (5)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (4)) (.leaf (8)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (6))) (.branch 46 (.leaf (3)) (.branch 47 (.leaf (1)) (.leaf (2)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (7))) (.branch 51 (.leaf (5)) (.branch 52 (.leaf (4)) (.leaf (1))))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (6))) (.branch 56 (.leaf (3)) (.branch 57 (.leaf (8)) (.leaf (2))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (5)) (.branch 62 (.leaf (4)) (.leaf (7))))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (3))) (.branch 66 (.leaf (6)) (.branch 67 (.leaf (1)) (.leaf (2)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (0)) (.leaf (8))) (.branch 71 (.leaf (4)) (.branch 72 (.leaf (5)) (.leaf (1))))) (.branch 75 (.branch 74 (.leaf (0)) (.leaf (3))) (.branch 76 (.leaf (7)) (.branch 77 (.leaf (2)) (.leaf (6)))))))))
  code := certificateP9_4191
  counts := ![(.branch 35 (.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))) (.branch 54 (.branch 44 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 49 (.leaf (10)) (.leaf (11)))) (.branch 64 (.branch 59 (.leaf (12)) (.leaf (13))) (.branch 69 (.leaf (14)) (.branch 74 (.leaf (15)) (.leaf (16))))))),
  (.branch 34 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 53 (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))) (.branch 67 (.branch 60 (.leaf (9)) (.leaf (10))) (.branch 73 (.leaf (11)) (.leaf (12)))))),
  (.branch 38 (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 58 (.branch 48 (.leaf (4)) (.leaf (5))) (.branch 68 (.leaf (6)) (.branch 77 (.leaf (7)) (.leaf (8)))))),
  (.branch 36 (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 65 (.leaf (6)) (.branch 75 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.branch 71 (.leaf (7)) (.leaf (8)))))),
  (.branch 39 (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 61 (.branch 51 (.leaf (4)) (.leaf (5))) (.branch 72 (.leaf (6)) (.leaf (7))))),
  (.branch 45 (.branch 22 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))) (.branch 66 (.branch 55 (.leaf (4)) (.leaf (5))) (.branch 78 (.leaf (6)) (.leaf (7))))),
  (.branch 37 (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 63 (.branch 50 (.leaf (3)) (.leaf (4))) (.branch 76 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 70 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-31)) (.leaf (-38)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 14 (.leaf (-10)) (.leaf (-11)))),
  (.branch 9 (.leaf (0)) (.branch 38 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (-11)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.branch 32 (.leaf (-27)) (.leaf (-28)))),
  (.branch 27 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-14)))) (.branch 61 (.leaf (-15)) (.branch 72 (.leaf (-16)) (.leaf (-17))))),
  (.branch 33 (.branch 22 (.leaf (0)) (.leaf (-2))) (.branch 55 (.leaf (-3)) (.branch 66 (.leaf (-5)) (.leaf (-6))))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 65 (.branch 50 (.branch 45 (.leaf (-38)) (.leaf (-37))) (.branch 55 (.leaf (-36)) (.branch 60 (.leaf (-35)) (.leaf (-34))))) (.branch 75 (.branch 70 (.leaf (-33)) (.leaf (-32))) (.branch 76 (.leaf (-24)) (.branch 77 (.leaf (-16)) (.leaf (-8)))))),
  (.branch 75 (.branch 54 (.leaf (-11)) (.branch 74 (.leaf (-10)) (.leaf (-8)))) (.branch 76 (.leaf (-6)) (.branch 77 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-4)),
  (.branch 76 (.branch 66 (.leaf (-13)) (.leaf (-12))) (.branch 77 (.leaf (-8)) (.leaf (-4)))),
  (.branch 74 (.branch 72 (.leaf (-28)) (.branch 73 (.leaf (-24)) (.leaf (-20)))) (.branch 76 (.branch 75 (.leaf (-16)) (.leaf (-12))) (.branch 77 (.leaf (-8)) (.leaf (-4))))),
  (.branch 75 (.branch 73 (.leaf (-17)) (.branch 74 (.leaf (-15)) (.leaf (-13)))) (.branch 76 (.leaf (-11)) (.branch 77 (.leaf (-9)) (.leaf (-7))))),
  (.branch 68 (.branch 67 (.leaf (-6)) (.leaf (-4))) (.branch 69 (.leaf (-2)) (.leaf (0)))),
  (.branch 77 (.leaf (-2)) (.leaf (-1))),
  (.branch 73 (.branch 71 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 72 (.leaf (-7)) (.leaf (-6)))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_271_4192 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (7)) (.branch 8 (.leaf (4)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (1)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (8))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (5))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (4))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (7))) (.branch 27 (.leaf (6)) (.branch 28 (.leaf (1)) (.leaf (3)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (5)) (.leaf (4))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (8))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (2)) (.leaf (1)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (6)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (3))) (.branch 46 (.leaf (7)) (.branch 47 (.leaf (4)) (.leaf (1)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (5)) (.branch 52 (.leaf (1)) (.leaf (3))))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (8))) (.branch 56 (.leaf (2)) (.branch 57 (.leaf (1)) (.leaf (6))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (0)) (.leaf (4))) (.branch 61 (.leaf (3)) (.branch 62 (.leaf (1)) (.leaf (2))))) (.branch 65 (.branch 64 (.leaf (0)) (.leaf (7))) (.branch 66 (.leaf (5)) (.branch 67 (.leaf (1)) (.leaf (3)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (0)) (.leaf (2))) (.branch 71 (.leaf (1)) (.branch 72 (.leaf (6)) (.leaf (4))))) (.branch 75 (.branch 74 (.leaf (0)) (.leaf (8))) (.branch 76 (.leaf (3)) (.branch 77 (.leaf (2)) (.leaf (1)))))))))
  code := certificateP9_4192
  counts := ![(.branch 35 (.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))) (.branch 54 (.branch 44 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 49 (.leaf (10)) (.leaf (11)))) (.branch 64 (.branch 59 (.leaf (12)) (.leaf (13))) (.branch 69 (.leaf (14)) (.branch 74 (.leaf (15)) (.leaf (16))))))),
  (.branch 39 (.branch 18 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))) (.branch 57 (.branch 48 (.branch 41 (.leaf (8)) (.leaf (9))) (.branch 52 (.leaf (10)) (.leaf (11)))) (.branch 67 (.branch 62 (.leaf (12)) (.leaf (13))) (.branch 71 (.leaf (14)) (.branch 78 (.leaf (15)) (.leaf (16))))))),
  (.branch 38 (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))) (.branch 56 (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))) (.branch 70 (.branch 63 (.leaf (9)) (.leaf (10))) (.branch 77 (.leaf (11)) (.leaf (12)))))),
  (.branch 37 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 61 (.branch 45 (.leaf (5)) (.branch 53 (.leaf (6)) (.leaf (7)))) (.branch 68 (.leaf (8)) (.branch 76 (.leaf (9)) (.leaf (10)))))),
  (.branch 34 (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 60 (.branch 47 (.leaf (3)) (.leaf (4))) (.branch 73 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 3 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 66 (.leaf (4)) (.leaf (5))))),
  (.branch 42 (.branch 12 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 58 (.leaf (3)) (.branch 72 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 65 (.leaf (3)) (.leaf (4))))),
  (.branch 36 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.branch 75 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-31)) (.leaf (-38)))),
  (.branch 32 (.branch 18 (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))) (.branch 23 (.leaf (-6)) (.branch 28 (.leaf (-7)) (.leaf (-8))))) (.branch 57 (.branch 41 (.leaf (-10)) (.branch 52 (.leaf (-13)) (.leaf (-14)))) (.branch 67 (.branch 62 (.leaf (-15)) (.leaf (-16))) (.branch 71 (.leaf (-17)) (.leaf (-19)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 43 (.leaf (-9)) (.branch 56 (.leaf (-11)) (.leaf (-12))))),
  (.branch 6 (.leaf (0)) (.branch 29 (.leaf (-9)) (.leaf (-11)))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-14))) (.branch 33 (.leaf (-15)) (.branch 66 (.leaf (-18)) (.leaf (-19))))),
  (.branch 42 (.branch 12 (.leaf (0)) (.branch 27 (.leaf (-5)) (.leaf (-7)))) (.branch 58 (.leaf (-9)) (.branch 72 (.leaf (-10)) (.leaf (-13))))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (-25)) (.leaf (-26)))),
  (.branch 16 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 65 (.branch 50 (.branch 45 (.leaf (-38)) (.leaf (-37))) (.branch 55 (.leaf (-36)) (.branch 60 (.leaf (-35)) (.leaf (-34))))) (.branch 75 (.branch 70 (.leaf (-33)) (.leaf (-32))) (.branch 76 (.leaf (-24)) (.branch 77 (.leaf (-16)) (.leaf (-8)))))),
  (.branch 74 (.branch 72 (.leaf (-19)) (.branch 73 (.leaf (-18)) (.leaf (-17)))) (.branch 76 (.branch 75 (.leaf (-16)) (.leaf (-15))) (.branch 77 (.leaf (-14)) (.leaf (-13))))),
  (.branch 64 (.branch 57 (.leaf (-12)) (.leaf (-11))) (.branch 71 (.leaf (-10)) (.leaf (-9)))),
  (.branch 69 (.leaf (-11)) (.branch 77 (.leaf (-10)) (.leaf (-5)))),
  (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.branch 72 (.branch 69 (.branch 67 (.leaf (-19)) (.branch 68 (.leaf (-18)) (.leaf (-17)))) (.branch 70 (.leaf (-16)) (.branch 71 (.leaf (-15)) (.leaf (-14))))) (.branch 75 (.branch 73 (.leaf (-13)) (.branch 74 (.leaf (-12)) (.leaf (-11)))) (.branch 76 (.leaf (-10)) (.branch 77 (.leaf (-9)) (.leaf (-8)))))),
  (.branch 75 (.branch 73 (.leaf (-13)) (.branch 74 (.leaf (-12)) (.leaf (-11)))) (.branch 76 (.leaf (-10)) (.branch 77 (.leaf (-9)) (.leaf (-8))))),
  (.branch 71 (.branch 68 (.branch 66 (.leaf (-26)) (.branch 67 (.leaf (-24)) (.leaf (-22)))) (.branch 69 (.leaf (-20)) (.branch 70 (.leaf (-18)) (.leaf (-16))))) (.branch 74 (.branch 72 (.leaf (-14)) (.branch 73 (.leaf (-12)) (.leaf (-10)))) (.branch 76 (.branch 75 (.leaf (-8)) (.leaf (-6))) (.branch 77 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 76 (.branch 56 (.leaf (-7)) (.leaf (-6))) (.branch 77 (.leaf (-4)) (.leaf (-2))))]
def witnessP9_271_4193 : CycleWitness 9 where
  length := 78
  word := (.branch 39 (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (7))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (6)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (8)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (5))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (7)) (.leaf (0))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (6)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (8)) (.leaf (2))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (5)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (3)) (.leaf (0))) (.branch 32 (.leaf (7)) (.branch 33 (.leaf (0)) (.leaf (4))))) (.branch 36 (.branch 35 (.leaf (6)) (.leaf (1))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (8)))))))) (.branch 58 (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (3))) (.branch 42 (.leaf (5)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (4)) (.leaf (1))) (.branch 46 (.leaf (7)) (.branch 47 (.leaf (0)) (.leaf (2)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (6)) (.leaf (0))) (.branch 51 (.leaf (8)) (.branch 52 (.leaf (3)) (.leaf (0))))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (5))) (.branch 56 (.leaf (4)) (.branch 57 (.leaf (0)) (.leaf (7))))))) (.branch 68 (.branch 63 (.branch 60 (.branch 59 (.leaf (0)) (.leaf (2))) (.branch 61 (.leaf (6)) (.branch 62 (.leaf (1)) (.leaf (0))))) (.branch 65 (.branch 64 (.leaf (3)) (.leaf (8))) (.branch 66 (.leaf (0)) (.branch 67 (.leaf (4)) (.leaf (5)))))) (.branch 73 (.branch 70 (.branch 69 (.leaf (0)) (.leaf (2))) (.branch 71 (.leaf (1)) (.branch 72 (.leaf (7)) (.leaf (0))))) (.branch 75 (.branch 74 (.leaf (3)) (.leaf (6))) (.branch 76 (.leaf (0)) (.branch 77 (.leaf (8)) (.leaf (4)))))))))
  code := certificateP9_4193
  counts := ![(.branch 37 (.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 31 (.leaf (9)) (.branch 33 (.leaf (10)) (.leaf (11)))))) (.branch 57 (.branch 47 (.branch 40 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14)))) (.branch 50 (.leaf (15)) (.branch 53 (.leaf (16)) (.leaf (17))))) (.branch 66 (.branch 59 (.leaf (18)) (.branch 63 (.leaf (19)) (.leaf (20)))) (.branch 73 (.branch 69 (.leaf (21)) (.leaf (22))) (.branch 76 (.leaf (23)) (.leaf (24))))))),
  (.branch 36 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 54 (.branch 45 (.leaf (5)) (.leaf (6))) (.branch 62 (.leaf (7)) (.branch 71 (.leaf (8)) (.leaf (9)))))),
  (.branch 38 (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 60 (.branch 48 (.leaf (4)) (.leaf (5))) (.branch 70 (.leaf (6)) (.leaf (7))))),
  (.branch 41 (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))) (.branch 64 (.branch 52 (.leaf (4)) (.leaf (5))) (.branch 74 (.leaf (6)) (.leaf (7))))),
  (.branch 44 (.branch 22 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))) (.branch 67 (.branch 56 (.leaf (4)) (.leaf (5))) (.branch 78 (.leaf (6)) (.leaf (7))))),
  (.branch 29 (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 68 (.leaf (5)) (.leaf (6))))),
  (.branch 35 (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 61 (.branch 49 (.leaf (3)) (.leaf (4))) (.branch 75 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 58 (.branch 46 (.leaf (3)) (.leaf (4))) (.branch 72 (.leaf (5)) (.leaf (6))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 65 (.branch 51 (.leaf (3)) (.leaf (4))) (.branch 77 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 33 (.leaf (-20)) (.branch 59 (.leaf (-22)) (.leaf (-24))))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-20)) (.leaf (-22)))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-29)) (.leaf (-30)))) (.branch 48 (.leaf (-31)) (.branch 70 (.leaf (-33)) (.leaf (-35))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (-13))) (.branch 74 (.leaf (-18)) (.leaf (-19)))),
  (.branch 22 (.leaf (0)) (.branch 44 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 25 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 70 (.branch 60 (.leaf (-24)) (.leaf (-23))) (.branch 77 (.leaf (-20)) (.leaf (-13)))),
  (.branch 74 (.branch 72 (.branch 63 (.leaf (-22)) (.leaf (-21))) (.branch 73 (.leaf (-18)) (.leaf (-15)))) (.branch 76 (.branch 75 (.leaf (-12)) (.leaf (-9))) (.branch 77 (.leaf (-6)) (.leaf (-3))))),
  (.branch 74 (.branch 72 (.branch 71 (.leaf (-35)) (.leaf (-31))) (.branch 73 (.leaf (-27)) (.leaf (-23)))) (.branch 76 (.branch 75 (.leaf (-19)) (.leaf (-15))) (.branch 77 (.leaf (-11)) (.leaf (-7))))),
  (.branch 76 (.branch 75 (.leaf (-19)) (.leaf (-15))) (.branch 77 (.leaf (-11)) (.leaf (-7)))),
  (.branch 45 (.leaf (-4)) (.branch 68 (.leaf (-2)) (.leaf (0)))),
  (.branch 73 (.branch 70 (.branch 69 (.leaf (-10)) (.leaf (-9))) (.branch 71 (.leaf (-8)) (.branch 72 (.leaf (-7)) (.leaf (-6))))) (.branch 75 (.branch 74 (.leaf (-5)) (.leaf (-4))) (.branch 76 (.leaf (-3)) (.branch 77 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 76 (.branch 62 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1)))),
  (.branch 74 (.branch 59 (.leaf (-7)) (.branch 73 (.leaf (-6)) (.leaf (-5)))) (.branch 76 (.branch 75 (.leaf (-4)) (.leaf (-3))) (.branch 77 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessP9_271 : Fin 38 → CycleWitness 9 := ![witnessP9_271_4156, witnessP9_271_4157, witnessP9_271_4158, witnessP9_271_4159, witnessP9_271_4160, witnessP9_271_4161, witnessP9_271_4162, witnessP9_271_4163, witnessP9_271_4164, witnessP9_271_4165, witnessP9_271_4166, witnessP9_271_4167, witnessP9_271_4168, witnessP9_271_4169, witnessP9_271_4170, witnessP9_271_4171, witnessP9_271_4172, witnessP9_271_4173, witnessP9_271_4174, witnessP9_271_4175, witnessP9_271_4176, witnessP9_271_4177, witnessP9_271_4178, witnessP9_271_4179, witnessP9_271_4180, witnessP9_271_4181, witnessP9_271_4182, witnessP9_271_4183, witnessP9_271_4184, witnessP9_271_4185, witnessP9_271_4186, witnessP9_271_4187, witnessP9_271_4188, witnessP9_271_4189, witnessP9_271_4190, witnessP9_271_4191, witnessP9_271_4192, witnessP9_271_4193]
end RealPinwheel.FiveSixths


