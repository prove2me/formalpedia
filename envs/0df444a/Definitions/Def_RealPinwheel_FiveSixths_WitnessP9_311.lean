-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_311
-- name    : RealPinwheel_FiveSixths_WitnessP9_311
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:31:54.34299+00:00
-- url     : https://prove2.me/theorems/f7812514-9d48-4e41-a245-5338c92f6b00
-- title:
--   Exact witness block P9_311
-- statement:
--   These exact witnesses represent words 6002 through 6058 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 6002–6058; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_311_6001 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (7))) (.branch 25 (.leaf (0)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (3)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (6))) (.branch 38 (.leaf (2)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (4)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (5)) (.branch 44 (.leaf (3)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (8))) (.branch 51 (.leaf (0)) (.leaf (3))))))))
  code := certificateP9_6001
  counts := ![(.branch 25 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))) (.branch 39 (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.branch 36 (.leaf (12)) (.leaf (13))))) (.branch 45 (.branch 42 (.leaf (14)) (.leaf (15))) (.branch 48 (.leaf (16)) (.branch 51 (.leaf (17)) (.leaf (18))))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-8))) (.branch 43 (.leaf (-11)) (.leaf (-13)))),
  (.branch 11 (.leaf (0)) (.leaf (-15))),
  (.branch 24 (.leaf (0)) (.leaf (-28))),
  (.branch 50 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 37 (.branch 31 (.branch 28 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 43 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.branch 49 (.leaf (-10)) (.leaf (-9)))))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 41 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))))),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 31 (.branch 27 (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26)))) (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.leaf (-22))))) (.branch 34 (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19)))) (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))))) (.branch 45 (.branch 41 (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_311_6002 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (8))) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (7))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (4)) (.leaf (6))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (8))) (.branch 38 (.leaf (2)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (5)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (4)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (6)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (7))))))))
  code := certificateP9_6002
  counts := ![(.branch 24 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 39 (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.branch 36 (.leaf (12)) (.leaf (13))))) (.branch 45 (.branch 42 (.leaf (14)) (.leaf (15))) (.branch 47 (.leaf (16)) (.branch 50 (.leaf (17)) (.leaf (18))))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 21 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (-34))) (.branch 40 (.leaf (-35)) (.leaf (-36)))),
  (.branch 14 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 48 (.leaf (-19)) (.branch 51 (.leaf (-18)) (.leaf (-9)))),
  (.branch 49 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 43 (.branch 41 (.leaf (-36)) (.branch 42 (.leaf (-33)) (.leaf (-30)))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 50 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_311_6003 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (8))) (.branch 12 (.leaf (2)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (7))) (.branch 25 (.leaf (3)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (5)) (.leaf (6))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (3)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (8))) (.branch 38 (.leaf (2)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (5)) (.leaf (3)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (6))))) (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (7))) (.branch 51 (.leaf (3)) (.leaf (5))))))))
  code := certificateP9_6003
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-10)))) (.branch 30 (.leaf (-11)) (.branch 43 (.leaf (-12)) (.leaf (-13))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-4)))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (-27))) (.branch 46 (.leaf (-29)) (.leaf (-30)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-2)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 24 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 49 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-10)) (.branch 51 (.leaf (-8)) (.leaf (-6))))),
  (.branch 50 (.branch 34 (.leaf (-17)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 48 (.branch 30 (.leaf (-17)) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 43 (.leaf (-4)) (.leaf (-3))),
  (.branch 49 (.branch 47 (.leaf (-30)) (.branch 48 (.leaf (-25)) (.leaf (-20)))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 21 (.leaf (-4)) (.branch 42 (.leaf (-3)) (.leaf (0)))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_311_6004 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (7)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (5)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (3)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (0))) (.branch 38 (.leaf (2)) (.leaf (8)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (3)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (5)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (6))))))))
  code := certificateP9_6004
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 32 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14))))) (.branch 45 (.branch 40 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17)))) (.branch 48 (.leaf (18)) (.branch 50 (.leaf (19)) (.leaf (20))))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 11 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-39))),
  (.branch 39 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 51 (.leaf (-10)) (.leaf (-5))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.leaf (-5)) (.branch 43 (.leaf (-4)) (.leaf (-3)))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 32 (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-39)) (.leaf (-38))) (.branch 16 (.leaf (-37)) (.leaf (-36)))) (.branch 19 (.branch 18 (.leaf (-35)) (.leaf (-34))) (.branch 20 (.leaf (-33)) (.branch 21 (.leaf (-32)) (.leaf (-31)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-30)) (.leaf (-29))) (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26))))) (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-21))))))) (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_311_6005 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (8)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (6)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (3))) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (7)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (4))) (.branch 51 (.leaf (0)) (.leaf (2))))))))
  code := certificateP9_6005
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 33 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14))))) (.branch 46 (.branch 40 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17)))) (.branch 48 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20))))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 11 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 29 (.leaf (-4)) (.branch 42 (.leaf (-5)) (.leaf (-6))))),
  (.branch 11 (.leaf (0)) (.leaf (-15))),
  (.branch 24 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-47))),
  (.branch 31 (.leaf (0)) (.leaf (-21))),
  (.branch 44 (.leaf (0)) (.leaf (-8))),
  (.branch 18 (.leaf (0)) (.leaf (-34)))]
  high := ![(.branch 41 (.leaf (-8)) (.branch 49 (.leaf (-7)) (.leaf (-5)))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 48 (.branch 43 (.leaf (-6)) (.leaf (-5))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-1)) (.leaf (0))))),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 28 (.branch 16 (.branch 10 (.branch 7 (.branch 6 (.leaf (-47)) (.leaf (-46))) (.branch 8 (.leaf (-45)) (.branch 9 (.leaf (-44)) (.leaf (-43))))) (.branch 13 (.branch 11 (.leaf (-42)) (.branch 12 (.leaf (-41)) (.leaf (-40)))) (.branch 14 (.leaf (-39)) (.branch 15 (.leaf (-38)) (.leaf (-37)))))) (.branch 22 (.branch 19 (.branch 17 (.leaf (-36)) (.branch 18 (.leaf (-35)) (.leaf (-34)))) (.branch 20 (.leaf (-33)) (.branch 21 (.leaf (-32)) (.leaf (-31))))) (.branch 25 (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))) (.branch 26 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25))))))) (.branch 40 (.branch 34 (.branch 31 (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-22)))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (-34)) (.leaf (-33))) (.branch 21 (.leaf (-32)) (.leaf (-31)))) (.branch 24 (.branch 23 (.leaf (-30)) (.leaf (-29))) (.branch 25 (.leaf (-28)) (.leaf (-27))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-25))) (.branch 29 (.leaf (-24)) (.leaf (-23)))) (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))))) (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_311_6006 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (7)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (5)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (4)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (3)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (6)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (8)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (2))))))))
  code := certificateP9_6006
  counts := ![(.branch 23 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 49 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 29 (.leaf (-4)) (.branch 42 (.leaf (-5)) (.leaf (-6))))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8))),
  (.branch 22 (.leaf (0)) (.leaf (-30))),
  (.branch 48 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 50 (.leaf (-12)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 46 (.leaf (-8)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 48 (.branch 43 (.leaf (-6)) (.leaf (-5))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-1)) (.leaf (0))))),
  (.leaf (-1)),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 37 (.branch 29 (.branch 25 (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))) (.branch 27 (.branch 26 (.leaf (-27)) (.leaf (-26))) (.branch 28 (.leaf (-25)) (.leaf (-24))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.leaf (-20)))) (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_311_6007 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (7))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (5)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (4))) (.branch 38 (.leaf (0)) (.leaf (6)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (5)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (4))) (.branch 51 (.leaf (0)) (.leaf (8))))))))
  code := certificateP9_6007
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 33 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14))))) (.branch 46 (.branch 40 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17)))) (.branch 48 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20))))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.branch 26 (.leaf (0)) (.leaf (-26))),
  (.leaf (0))]
  high := ![(.branch 41 (.leaf (-8)) (.branch 49 (.leaf (-7)) (.leaf (-5)))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (-26)) (.branch 28 (.leaf (-25)) (.leaf (-24)))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-21))))) (.branch 35 (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18)))) (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_311_6008 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (6)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (7)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (8)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (7)) (.leaf (4))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (8)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (3)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (6)) (.leaf (4))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (7)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (8))))))))
  code := certificateP9_6008
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-9)) (.leaf (-10)))),
  (.branch 23 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-7)))) (.branch 36 (.leaf (-8)) (.branch 49 (.leaf (-9)) (.leaf (-10))))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (-37))) (.branch 39 (.leaf (-38)) (.leaf (-39)))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (-25)) (.leaf (-26)))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 44 (.leaf (-10)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 50 (.leaf (-10)) (.branch 51 (.leaf (-8)) (.leaf (-6)))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-39)) (.branch 41 (.leaf (-36)) (.leaf (-33)))) (.branch 43 (.leaf (-30)) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 47 (.branch 45 (.branch 27 (.leaf (-26)) (.leaf (-24))) (.branch 46 (.leaf (-21)) (.leaf (-18)))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0))]
def witnessP9_311_6009 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (7)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (6)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (3)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (2))) (.branch 38 (.leaf (0)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (2)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (8)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (1)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (1)) (.leaf (5))))))))
  code := certificateP9_6009
  counts := ![(.branch 23 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 45 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 49 (.leaf (13)) (.leaf (14)))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 43 (.leaf (11)) (.leaf (12))) (.branch 51 (.leaf (13)) (.leaf (14)))))),
  (.branch 24 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 15 (.leaf (-24)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.leaf (-12))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-34))),
  (.branch 44 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 46 (.branch 42 (.leaf (-25)) (.leaf (-23))) (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-14)) (.leaf (-7))))),
  (.branch 44 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 48 (.leaf (-9)) (.leaf (-7)))),
  (.branch 51 (.leaf (-6)) (.leaf (-3))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (-34)) (.leaf (-33))) (.branch 21 (.leaf (-32)) (.leaf (-31)))) (.branch 24 (.branch 23 (.leaf (-30)) (.leaf (-29))) (.branch 25 (.leaf (-28)) (.leaf (-27))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-25))) (.branch 29 (.leaf (-24)) (.leaf (-23)))) (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))))) (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_311_6010 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (7)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (4)) (.branch 34 (.leaf (0)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (3)) (.leaf (8)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (4)) (.branch 44 (.leaf (0)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (0)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (4)) (.leaf (6))))))))
  code := certificateP9_6010
  counts := ![(.branch 24 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 31 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 20 (.leaf (-6)) (.branch 46 (.leaf (-7)) (.leaf (-8))))),
  (.branch 7 (.leaf (0)) (.branch 33 (.leaf (-2)) (.leaf (-3)))),
  (.branch 26 (.leaf (0)) (.leaf (-26))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-39))),
  (.branch 39 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 41 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 49 (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (-26)) (.branch 28 (.leaf (-25)) (.leaf (-24)))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-21))))) (.branch 35 (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18)))) (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0)),
  (.branch 32 (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-39)) (.leaf (-38))) (.branch 16 (.leaf (-37)) (.leaf (-36)))) (.branch 19 (.branch 18 (.leaf (-35)) (.leaf (-34))) (.branch 20 (.leaf (-33)) (.branch 21 (.leaf (-32)) (.leaf (-31)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-30)) (.leaf (-29))) (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26))))) (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-21))))))) (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_311_6011 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (5)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (7)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (5)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (0)) (.leaf (4))))) (.branch 35 (.branch 33 (.leaf (6)) (.branch 34 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (5)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (0)) (.leaf (4))))) (.branch 48 (.branch 46 (.leaf (8)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (5)) (.leaf (4))))))))
  code := certificateP9_6011
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 46 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-32))),
  (.branch 46 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 50 (.branch 45 (.leaf (-11)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 44 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 46 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 28 (.branch 24 (.branch 22 (.branch 21 (.leaf (-32)) (.leaf (-31))) (.branch 23 (.leaf (-30)) (.leaf (-29)))) (.branch 26 (.branch 25 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.leaf (-25))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-24)) (.leaf (-23))) (.branch 31 (.leaf (-22)) (.leaf (-21)))) (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-17)))))) (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_311_6012 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (8)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (6)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (7))) (.branch 25 (.leaf (3)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (4)) (.branch 31 (.leaf (0)) (.leaf (8))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (6)) (.leaf (3)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (1)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (4)) (.leaf (7)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (6)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (8))) (.branch 51 (.leaf (4)) (.leaf (5))))))))
  code := certificateP9_6012
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 17 (.leaf (-18)) (.branch 22 (.leaf (-19)) (.leaf (-20))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 19 (.leaf (-7)) (.branch 45 (.leaf (-8)) (.leaf (-9))))),
  (.branch 4 (.leaf (0)) (.branch 35 (.leaf (-32)) (.leaf (-33)))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-23))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (-3)) (.leaf (-6))))]
  high := ![(.branch 50 (.branch 45 (.leaf (-11)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 48 (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7)))) (.branch 50 (.branch 49 (.leaf (-6)) (.leaf (-5))) (.branch 51 (.leaf (-4)) (.leaf (-3))))),
  (.branch 48 (.branch 36 (.leaf (-33)) (.branch 47 (.leaf (-30)) (.leaf (-25)))) (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 10 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 43 (.branch 7 (.leaf (-23)) (.branch 25 (.leaf (-22)) (.leaf (-21)))) (.branch 44 (.leaf (-19)) (.branch 45 (.leaf (-17)) (.leaf (-15))))) (.branch 49 (.branch 47 (.leaf (-13)) (.branch 48 (.leaf (-11)) (.leaf (-9)))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 33 (.leaf (-6)) (.branch 51 (.leaf (-5)) (.leaf (-3))))]
def witnessP9_311_6013 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (3)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (5)) (.leaf (4)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (8))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (6))) (.branch 25 (.leaf (2)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (4)) (.branch 31 (.leaf (0)) (.leaf (7))))) (.branch 35 (.branch 33 (.leaf (5)) (.branch 34 (.leaf (3)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (4)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (6)) (.leaf (3)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (8))))) (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (5))) (.branch 51 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_6013
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))) (.branch 39 (.branch 17 (.leaf (-10)) (.leaf (-11))) (.branch 43 (.leaf (-12)) (.leaf (-13))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.leaf (-14))) (.branch 40 (.leaf (-18)) (.leaf (-20)))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 26 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 15 (.leaf (0)) (.leaf (-7))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (-31))) (.branch 41 (.leaf (-32)) (.leaf (-33)))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 49 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-10)) (.branch 51 (.leaf (-8)) (.leaf (-6))))),
  (.branch 49 (.branch 41 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-16)))) (.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-10)) (.leaf (-7))))),
  (.branch 30 (.leaf (-6)) (.leaf (-5))),
  (.branch 50 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-5)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 16 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 46 (.branch 43 (.branch 42 (.leaf (-33)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_311_6014 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (5)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (2)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (8)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 30 (.leaf (4)) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (2)) (.branch 34 (.leaf (6)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (3))) (.branch 38 (.leaf (5)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (2)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (4)) (.branch 44 (.leaf (3)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (7)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_6014
  counts := ![(.branch 24 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 39 (.branch 31 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 35 (.leaf (9)) (.leaf (10)))) (.branch 46 (.branch 42 (.leaf (11)) (.leaf (12))) (.branch 50 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.leaf (7))))),
  (.branch 29 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 47 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-19))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 40 (.leaf (-31)) (.leaf (-32)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 47 (.leaf (0)) (.leaf (-5))),
  (.branch 21 (.leaf (0)) (.leaf (-31)))]
  high := ![(.branch 43 (.branch 28 (.leaf (-19)) (.leaf (-18))) (.branch 47 (.leaf (-16)) (.branch 51 (.leaf (-14)) (.leaf (-7))))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.branch 41 (.leaf (-32)) (.leaf (-28))) (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-14)) (.leaf (-7))))),
  (.branch 30 (.branch 15 (.leaf (-6)) (.leaf (-5))) (.branch 45 (.leaf (-4)) (.leaf (0)))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 43 (.branch 38 (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 28 (.branch 24 (.branch 22 (.leaf (-31)) (.branch 23 (.leaf (-30)) (.leaf (-29)))) (.branch 26 (.branch 25 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.leaf (-25))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-24)) (.leaf (-23))) (.branch 31 (.leaf (-22)) (.leaf (-21)))) (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-17)))))) (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_311_6015 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (6)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (8)) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (4)) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (7)) (.branch 34 (.leaf (6)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (1))) (.branch 38 (.leaf (3)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (2)) (.leaf (5)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (4))))) (.branch 48 (.branch 46 (.leaf (8)) (.branch 47 (.leaf (0)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (6)) (.leaf (3))))))))
  code := certificateP9_6015
  counts := ![(.branch 24 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 39 (.branch 31 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 35 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 43 (.leaf (11)) (.leaf (12))) (.branch 50 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 27 (.leaf (-14)) (.leaf (-17)))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))) (.branch 40 (.branch 18 (.leaf (-8)) (.leaf (-9))) (.branch 44 (.leaf (-10)) (.leaf (-11))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 41 (.leaf (-15)) (.leaf (-17)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 30 (.leaf (-10)) (.leaf (-12)))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (-28))) (.branch 42 (.leaf (-29)) (.leaf (-30)))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 28 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-11)))),
  (.branch 50 (.branch 45 (.leaf (-11)) (.leaf (-10))) (.branch 51 (.leaf (-8)) (.leaf (-6)))),
  (.branch 49 (.branch 42 (.leaf (-17)) (.leaf (-16))) (.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-10)) (.leaf (-7))))),
  (.branch 39 (.leaf (-1)) (.leaf (0))),
  (.branch 48 (.branch 46 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9)))) (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5))))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-30)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 17 (.leaf (-4)) (.leaf (-3))),
  (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_311_6016 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (4)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (7))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (2)) (.branch 28 (.leaf (0)) (.leaf (4)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (5)) (.branch 34 (.leaf (0)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (0))) (.branch 38 (.leaf (2)) (.leaf (6)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (4)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (5)) (.branch 47 (.leaf (0)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (8))))))))
  code := certificateP9_6016
  counts := ![(.branch 24 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 31 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 51 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 45 (.leaf (9)) (.branch 50 (.leaf (10)) (.leaf (11)))))),
  (.branch 27 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 48 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 24 (.branch 11 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 14 (.leaf (-6)) (.leaf (-7)))) (.branch 37 (.branch 34 (.leaf (-8)) (.leaf (-9))) (.branch 43 (.leaf (-10)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 25 (.leaf (-14)) (.leaf (-19)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 48 (.leaf (-4)) (.leaf (-6)))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.branch 26 (.leaf (0)) (.leaf (-26))),
  (.leaf (0))]
  high := ![(.branch 44 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))),
  (.branch 36 (.branch 26 (.leaf (-19)) (.branch 31 (.leaf (-18)) (.leaf (-17)))) (.branch 46 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.leaf (-9))))),
  (.branch 50 (.branch 49 (.leaf (-6)) (.leaf (-5))) (.branch 51 (.leaf (-4)) (.leaf (-3)))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 48 (.branch 20 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (-26)) (.branch 28 (.leaf (-25)) (.leaf (-24)))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-21))))) (.branch 35 (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18)))) (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_311_6017 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (7)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (8)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (7)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (8)) (.leaf (4))) (.branch 25 (.leaf (3)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (5)) (.branch 31 (.leaf (7)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (3)) (.branch 34 (.leaf (1)) (.leaf (4)))) (.branch 37 (.branch 36 (.leaf (8)) (.leaf (0))) (.branch 38 (.leaf (2)) (.leaf (6)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (5)) (.branch 41 (.leaf (1)) (.leaf (3)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (7)) (.leaf (4))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (8)) (.leaf (5))) (.branch 51 (.leaf (3)) (.leaf (6))))))))
  code := certificateP9_6017
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 45 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-21))) (.branch 11 (.leaf (-22)) (.leaf (-23)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (-32))) (.branch 24 (.leaf (-34)) (.leaf (-36)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (-7))) (.branch 50 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 49 (.branch 38 (.leaf (-23)) (.leaf (-20))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.leaf (-5)) (.branch 43 (.leaf (-4)) (.leaf (-3)))),
  (.branch 48 (.branch 46 (.branch 25 (.leaf (-36)) (.leaf (-35))) (.branch 47 (.leaf (-30)) (.leaf (-25)))) (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 51 (.leaf (-10)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_311_6018 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (4)) (.leaf (7)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (8)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (5)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (7)) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (3)) (.branch 34 (.leaf (8)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (1))) (.branch 38 (.leaf (4)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (6)) (.branch 44 (.leaf (0)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (7)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (1))) (.branch 51 (.leaf (4)) (.leaf (8))))))))
  code := certificateP9_6018
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-40)) (.leaf (-41)))),
  (.branch 8 (.leaf (0)) (.leaf (-28))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (-13))) (.branch 47 (.leaf (-14)) (.leaf (-15)))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 46 (.leaf (-8)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 50 (.branch 43 (.leaf (-7)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 45 (.branch 41 (.branch 22 (.leaf (-41)) (.branch 40 (.leaf (-39)) (.leaf (-36)))) (.branch 43 (.branch 42 (.leaf (-33)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 47 (.branch 44 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 35 (.leaf (-2)) (.leaf (0)))]
def witnessP9_311_6019 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (5)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (5)) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (8)) (.branch 34 (.leaf (0)) (.leaf (4)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (2)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (5)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (6))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (0))) (.branch 51 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_6019
  counts := ![(.branch 24 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 31 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 48 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 51 (.leaf (13)) (.leaf (14)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 43 (.leaf (-19)) (.leaf (-21)))),
  (.branch 2 (.leaf (0)) (.branch 28 (.leaf (-9)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-10)))),
  (.branch 19 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-45))),
  (.branch 33 (.leaf (0)) (.leaf (-19)))]
  high := ![(.branch 44 (.leaf (-21)) (.branch 51 (.leaf (-18)) (.leaf (-11)))),
  (.branch 29 (.leaf (-12)) (.leaf (-11))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 50 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-45)) (.leaf (-44))) (.branch 10 (.leaf (-43)) (.branch 11 (.leaf (-42)) (.leaf (-41))))) (.branch 15 (.branch 13 (.leaf (-40)) (.branch 14 (.leaf (-39)) (.leaf (-38)))) (.branch 16 (.leaf (-37)) (.branch 17 (.leaf (-36)) (.leaf (-35)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-34)) (.leaf (-33))) (.branch 21 (.leaf (-32)) (.branch 22 (.leaf (-31)) (.leaf (-30))))) (.branch 26 (.branch 24 (.leaf (-29)) (.branch 25 (.leaf (-28)) (.leaf (-27)))) (.branch 27 (.leaf (-26)) (.branch 28 (.leaf (-25)) (.leaf (-24))))))) (.branch 40 (.branch 34 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_311_6020 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (7)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (3)) (.leaf (0)))) (.branch 17 (.leaf (8)) (.branch 18 (.leaf (4)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (7))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 30 (.leaf (6)) (.branch 31 (.leaf (0)) (.leaf (4))))) (.branch 35 (.branch 33 (.leaf (2)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (8)) (.leaf (3))) (.branch 38 (.leaf (0)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (2)) (.leaf (0)))) (.branch 43 (.leaf (7)) (.branch 44 (.leaf (4)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (6)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (8))))))))
  code := certificateP9_6020
  counts := ![(.branch 24 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 35 (.leaf (9)) (.leaf (10)))) (.branch 46 (.branch 42 (.leaf (11)) (.leaf (12))) (.branch 50 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 29 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-19)) (.leaf (-20)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 14 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 25 (.leaf (-14)) (.leaf (-17)))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (-2))) (.branch 51 (.leaf (-5)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-40))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (-13)) (.leaf (-14)))),
  (.branch 26 (.branch 10 (.leaf (0)) (.leaf (-8))) (.branch 43 (.leaf (-10)) (.leaf (-11)))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 43 (.branch 39 (.leaf (-20)) (.leaf (-18))) (.branch 47 (.leaf (-16)) (.branch 51 (.leaf (-14)) (.leaf (-7))))),
  (.branch 49 (.branch 41 (.leaf (-11)) (.branch 48 (.leaf (-10)) (.leaf (-8)))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 42 (.branch 26 (.leaf (-17)) (.branch 34 (.leaf (-16)) (.leaf (-15)))) (.branch 50 (.leaf (-14)) (.branch 51 (.leaf (-11)) (.leaf (-8))))),
  (.leaf (-8)),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 41 (.branch 5 (.leaf (-40)) (.branch 40 (.leaf (-39)) (.leaf (-36)))) (.branch 43 (.branch 42 (.leaf (-33)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 31 (.leaf (-14)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8)))) (.branch 49 (.branch 48 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 18 (.leaf (-1)) (.leaf (0)))]
def witnessP9_311_6021 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (8)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (5)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (4)) (.leaf (7)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (6)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (5)) (.branch 31 (.leaf (0)) (.leaf (8))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (4)))) (.branch 37 (.branch 36 (.leaf (6)) (.leaf (0))) (.branch 38 (.leaf (1)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (7)) (.branch 41 (.leaf (0)) (.leaf (2)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (5)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (4)) (.leaf (8)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (6)) (.leaf (3))))))))
  code := certificateP9_6021
  counts := ![(.branch 23 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 31 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 45 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 49 (.leaf (13)) (.leaf (14)))))),
  (.branch 24 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 11 (.leaf (-17)) (.branch 37 (.leaf (-21)) (.leaf (-24))))),
  (.branch 24 (.branch 2 (.leaf (0)) (.branch 20 (.leaf (-8)) (.leaf (-10)))) (.branch 46 (.branch 28 (.leaf (-12)) (.leaf (-14))) (.branch 50 (.leaf (-16)) (.leaf (-18))))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.branch 36 (.leaf (-4)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (-23)) (.leaf (-26)))),
  (.branch 14 (.leaf (0)) (.branch 48 (.leaf (-7)) (.leaf (-9))))]
  high := ![(.branch 46 (.branch 38 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22)))) (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-16)) (.leaf (-11))))),
  (.branch 51 (.leaf (-18)) (.leaf (-15))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.branch 45 (.branch 31 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.leaf (-6)) (.leaf (-5))),
  (.branch 45 (.branch 42 (.branch 23 (.leaf (-26)) (.branch 41 (.leaf (-25)) (.leaf (-23)))) (.branch 43 (.leaf (-21)) (.branch 44 (.leaf (-19)) (.leaf (-17))))) (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-13)) (.leaf (-11)))) (.branch 50 (.branch 49 (.leaf (-9)) (.leaf (-7))) (.branch 51 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 50 (.branch 49 (.leaf (-9)) (.leaf (-7))) (.branch 51 (.leaf (-5)) (.leaf (-3))))]
def witnessP9_311_6022 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (7)) (.leaf (2))) (.branch 12 (.leaf (5)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (6)) (.branch 18 (.leaf (2)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (8)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 30 (.leaf (6)) (.branch 31 (.leaf (0)) (.leaf (4))))) (.branch 35 (.branch 33 (.leaf (2)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (7)) (.leaf (3))) (.branch 38 (.leaf (5)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (2)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (6)) (.branch 44 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (8)) (.leaf (0))) (.branch 51 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_6022
  counts := ![(.branch 24 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 39 (.branch 31 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 35 (.leaf (9)) (.leaf (10)))) (.branch 46 (.branch 42 (.leaf (11)) (.leaf (12))) (.branch 50 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.leaf (7))))),
  (.branch 29 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-19))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 40 (.leaf (-31)) (.leaf (-32)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-16))),
  (.branch 23 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 43 (.branch 28 (.leaf (-19)) (.leaf (-18))) (.branch 47 (.leaf (-16)) (.branch 51 (.leaf (-14)) (.leaf (-7))))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 41 (.leaf (-32)) (.leaf (-28))) (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-14)) (.leaf (-7))))),
  (.branch 30 (.branch 15 (.leaf (-6)) (.leaf (-5))) (.branch 45 (.leaf (-4)) (.leaf (0)))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_311_6023 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (8)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (6)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (7)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (6)) (.branch 31 (.leaf (0)) (.leaf (5))))) (.branch 35 (.branch 33 (.leaf (8)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (4))) (.branch 38 (.leaf (0)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (7)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (6)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (5)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (4))) (.branch 51 (.leaf (8)) (.leaf (3))))))))
  code := certificateP9_6023
  counts := ![(.branch 23 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 35 (.leaf (9)) (.leaf (10)))) (.branch 45 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 49 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 15 (.leaf (-16)) (.branch 41 (.leaf (-20)) (.leaf (-23))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 14 (.leaf (-10)) (.leaf (-11)))),
  (.branch 22 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 48 (.leaf (-14)) (.leaf (-16)))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 46 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-16)) (.leaf (-11))))),
  (.branch 49 (.branch 41 (.leaf (-11)) (.branch 48 (.leaf (-10)) (.leaf (-8)))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-13))) (.branch 51 (.leaf (-10)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 48 (.branch 33 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.branch 45 (.branch 31 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.branch 43 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 34 (.leaf (-5)) (.leaf (-3)))]
def witnessP9_311_6024 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (3)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (6)) (.branch 31 (.leaf (3)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (2)) (.leaf (8)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (1)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (3)))) (.branch 43 (.leaf (5)) (.branch 44 (.leaf (2)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (3)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_6024
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 29 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-6)) (.branch 41 (.leaf (-7)) (.leaf (-8))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 13 (.leaf (-12)) (.branch 18 (.leaf (-13)) (.leaf (-14))))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 22 (.leaf (0)) (.leaf (-4))),
  (.branch 17 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-22))),
  (.branch 9 (.leaf (0)) (.leaf (-43))),
  (.branch 35 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 50 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 42 (.leaf (-8)) (.branch 47 (.leaf (-7)) (.leaf (-6)))),
  (.branch 45 (.leaf (-14)) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.branch 35 (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))) (.branch 38 (.branch 36 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-43)) (.leaf (-42))) (.branch 12 (.leaf (-41)) (.branch 13 (.leaf (-40)) (.leaf (-39))))) (.branch 16 (.branch 15 (.leaf (-38)) (.leaf (-37))) (.branch 17 (.leaf (-36)) (.branch 18 (.leaf (-35)) (.leaf (-34)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-33)) (.leaf (-32))) (.branch 22 (.leaf (-31)) (.branch 23 (.leaf (-30)) (.leaf (-29))))) (.branch 27 (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26)))) (.branch 28 (.leaf (-25)) (.branch 29 (.leaf (-24)) (.leaf (-23))))))) (.branch 41 (.branch 35 (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))) (.branch 38 (.branch 36 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_311_6025 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (8)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (6)) (.branch 18 (.leaf (4)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (5)) (.leaf (7)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 30 (.leaf (6)) (.branch 31 (.leaf (5)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (2)) (.leaf (8)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (1)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (5)))) (.branch 43 (.leaf (6)) (.branch 44 (.leaf (2)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (3)) (.leaf (7)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (4))) (.branch 51 (.leaf (1)) (.leaf (5))))))))
  code := certificateP9_6025
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 44 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 11 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-6)) (.branch 41 (.leaf (-7)) (.leaf (-8))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (-37))) (.branch 44 (.leaf (-39)) (.leaf (-40)))),
  (.branch 5 (.leaf (0)) (.leaf (-27))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (-12)) (.leaf (-14)))),
  (.branch 31 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 22 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 50 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 42 (.leaf (-8)) (.branch 47 (.leaf (-7)) (.leaf (-6)))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-40)) (.leaf (-35))) (.branch 47 (.leaf (-30)) (.leaf (-25)))) (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 48 (.branch 6 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25)))) (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 40 (.branch 19 (.leaf (-14)) (.leaf (-13))) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_311_6026 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (8)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (7)) (.branch 18 (.leaf (4)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (6)) (.branch 21 (.leaf (5)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (8)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 30 (.leaf (7)) (.branch 31 (.leaf (5)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (6)) (.branch 34 (.leaf (2)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (8)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (5)))) (.branch 43 (.leaf (7)) (.branch 44 (.leaf (2)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (6)) (.branch 47 (.leaf (3)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (4))) (.branch 51 (.leaf (8)) (.leaf (5))))))))
  code := certificateP9_6026
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 44 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 11 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-10))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (-37))) (.branch 44 (.leaf (-39)) (.leaf (-40)))),
  (.branch 5 (.leaf (0)) (.leaf (-27))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (-12)) (.leaf (-14)))),
  (.branch 31 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 50 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-40)) (.leaf (-35))) (.branch 47 (.leaf (-30)) (.leaf (-25)))) (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 48 (.branch 6 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25)))) (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 40 (.branch 19 (.leaf (-14)) (.leaf (-13))) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_311_6027 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (8))) (.branch 12 (.leaf (1)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (6)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (7))) (.branch 25 (.leaf (0)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (5))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (8))) (.branch 38 (.leaf (1)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (3)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (6)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (4)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (7))) (.branch 51 (.leaf (0)) (.leaf (2))))))))
  code := certificateP9_6027
  counts := ![(.branch 25 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))) (.branch 39 (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.branch 36 (.leaf (12)) (.leaf (13))))) (.branch 45 (.branch 42 (.leaf (14)) (.leaf (15))) (.branch 48 (.leaf (16)) (.branch 51 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 31 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 35 (.leaf (9)) (.leaf (10)))) (.branch 46 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 49 (.leaf (13)) (.leaf (14)))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))) (.branch 38 (.branch 15 (.leaf (-4)) (.leaf (-5))) (.branch 41 (.leaf (-6)) (.leaf (-7))))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (-4)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 18 (.leaf (0)) (.leaf (-8))),
  (.branch 24 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 37 (.branch 31 (.branch 28 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 43 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.branch 49 (.leaf (-10)) (.leaf (-9)))))),
  (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))),
  (.branch 35 (.leaf (-2)) (.branch 44 (.leaf (-1)) (.leaf (0)))),
  (.branch 45 (.branch 42 (.branch 22 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10))))) (.branch 48 (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7)))) (.branch 50 (.branch 49 (.leaf (-6)) (.leaf (-5))) (.branch 51 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 49 (.branch 48 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3))))),
  (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_311_6028 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (5)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (6)) (.leaf (7))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (5)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (0))) (.branch 38 (.leaf (3)) (.leaf (8)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (6)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (5)) (.leaf (7))))))))
  code := certificateP9_6028
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 32 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14))))) (.branch 45 (.branch 40 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17)))) (.branch 48 (.leaf (18)) (.branch 50 (.leaf (19)) (.leaf (20))))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 11 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-2)) (.leaf (-4)))) (.branch 36 (.leaf (-5)) (.branch 49 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-43)) (.leaf (-44)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (-16))) (.branch 46 (.leaf (-17)) (.leaf (-18)))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 51 (.leaf (-10)) (.leaf (-5))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))),
  (.branch 44 (.branch 40 (.branch 21 (.leaf (-44)) (.branch 39 (.leaf (-42)) (.leaf (-39)))) (.branch 42 (.branch 41 (.leaf (-36)) (.leaf (-33))) (.branch 43 (.leaf (-30)) (.leaf (-27))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-24)) (.leaf (-21))) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.leaf (-5)) (.leaf (-3))),
  (.branch 46 (.branch 43 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (0)),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_311_6029 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (5)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (5)) (.branch 34 (.leaf (0)) (.leaf (8)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (4)) (.leaf (0)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (6)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_6029
  counts := ![(.branch 24 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 46 (.branch 42 (.leaf (11)) (.leaf (12))) (.branch 50 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 30 (.leaf (-18)) (.leaf (-21)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-12))) (.branch 14 (.leaf (-14)) (.branch 40 (.leaf (-18)) (.leaf (-20))))),
  (.branch 21 (.branch 13 (.leaf (0)) (.branch 17 (.leaf (-3)) (.leaf (-5)))) (.branch 43 (.branch 39 (.leaf (-7)) (.leaf (-9))) (.branch 47 (.leaf (-11)) (.leaf (-13))))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-11)) (.leaf (-13)))),
  (.branch 7 (.leaf (0)) (.branch 41 (.leaf (-21)) (.leaf (-23)))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 22 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-43))),
  (.branch 35 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 39 (.branch 31 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19)))) (.branch 47 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 51 (.leaf (-16)) (.leaf (-11))))),
  (.branch 50 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 51 (.leaf (-14)) (.leaf (-9)))),
  (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-10))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-4)) (.leaf (-1))))),
  (.branch 47 (.branch 45 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))))),
  (.branch 46 (.branch 43 (.branch 42 (.leaf (-23)) (.leaf (-21))) (.branch 44 (.leaf (-19)) (.branch 45 (.leaf (-17)) (.leaf (-15))))) (.branch 49 (.branch 47 (.leaf (-13)) (.branch 48 (.leaf (-11)) (.leaf (-9)))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 16 (.leaf (-5)) (.branch 34 (.leaf (-4)) (.leaf (-3)))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-43)) (.leaf (-42))) (.branch 12 (.leaf (-41)) (.branch 13 (.leaf (-40)) (.leaf (-39))))) (.branch 16 (.branch 15 (.leaf (-38)) (.leaf (-37))) (.branch 17 (.leaf (-36)) (.branch 18 (.leaf (-35)) (.leaf (-34)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-33)) (.leaf (-32))) (.branch 22 (.leaf (-31)) (.branch 23 (.leaf (-30)) (.leaf (-29))))) (.branch 27 (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26)))) (.branch 28 (.leaf (-25)) (.branch 29 (.leaf (-24)) (.leaf (-23))))))) (.branch 41 (.branch 35 (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))) (.branch 38 (.branch 36 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_311_6030 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (7))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (6)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (4))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (3)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (0))) (.branch 38 (.leaf (5)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (3)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (8))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (6)) (.leaf (2))))))))
  code := certificateP9_6030
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 31 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.branch 20 (.leaf (-3)) (.leaf (-4))))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 12 (.leaf (0)) (.leaf (-14))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 19 (.leaf (0)) (.leaf (-33))),
  (.branch 45 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 44 (.leaf (-10)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 50 (.branch 34 (.leaf (-17)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 47 (.leaf (-4)) (.leaf (0))),
  (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 41 (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 35 (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (-33)) (.leaf (-32))) (.branch 22 (.leaf (-31)) (.leaf (-30)))) (.branch 25 (.branch 24 (.leaf (-29)) (.leaf (-28))) (.branch 26 (.leaf (-27)) (.leaf (-26))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.leaf (-22)))) (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.leaf (-18)))))) (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_311_6031 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (4))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (6)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (8))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (7))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (6)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (4))) (.branch 38 (.leaf (3)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (5)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (8))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (4))) (.branch 51 (.leaf (6)) (.leaf (2))))))))
  code := certificateP9_6031
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 31 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-10)))) (.branch 30 (.leaf (-11)) (.branch 43 (.leaf (-12)) (.leaf (-13))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.branch 20 (.leaf (-3)) (.leaf (-4))))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (-28))) (.branch 42 (.leaf (-29)) (.leaf (-30)))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 49 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-10)) (.branch 51 (.leaf (-8)) (.leaf (-6))))),
  (.branch 50 (.branch 34 (.leaf (-17)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 47 (.leaf (-4)) (.leaf (0))),
  (.branch 48 (.branch 30 (.leaf (-17)) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-30)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 17 (.leaf (-4)) (.leaf (-3))),
  (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_311_6032 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (5)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (7))) (.branch 25 (.leaf (5)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (4)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (3)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (6))) (.branch 38 (.leaf (5)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (3)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (4)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (8))) (.branch 51 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_6032
  counts := ![(.branch 23 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 49 (.leaf (15)) (.leaf (16))))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-15))),
  (.branch 24 (.leaf (0)) (.leaf (-28))),
  (.branch 50 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 50 (.leaf (-12)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 46 (.leaf (-1)) (.leaf (0))),
  (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 31 (.branch 27 (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26)))) (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.leaf (-22))))) (.branch 34 (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19)))) (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))))) (.branch 45 (.branch 41 (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_311_6033 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (8)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (6)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (2)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (3)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (7)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (0)) (.leaf (2))))))))
  code := certificateP9_6033
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 32 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14))))) (.branch 45 (.branch 40 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17)))) (.branch 48 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20))))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-47))),
  (.branch 31 (.leaf (0)) (.leaf (-21))),
  (.branch 44 (.leaf (0)) (.leaf (-8))),
  (.branch 18 (.leaf (0)) (.leaf (-34)))]
  high := ![(.branch 46 (.leaf (-9)) (.branch 49 (.leaf (-7)) (.leaf (-5)))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 50 (.branch 43 (.leaf (-7)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 28 (.branch 16 (.branch 10 (.branch 7 (.branch 6 (.leaf (-47)) (.leaf (-46))) (.branch 8 (.leaf (-45)) (.branch 9 (.leaf (-44)) (.leaf (-43))))) (.branch 13 (.branch 11 (.leaf (-42)) (.branch 12 (.leaf (-41)) (.leaf (-40)))) (.branch 14 (.leaf (-39)) (.branch 15 (.leaf (-38)) (.leaf (-37)))))) (.branch 22 (.branch 19 (.branch 17 (.leaf (-36)) (.branch 18 (.leaf (-35)) (.leaf (-34)))) (.branch 20 (.leaf (-33)) (.branch 21 (.leaf (-32)) (.leaf (-31))))) (.branch 25 (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))) (.branch 26 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25))))))) (.branch 40 (.branch 34 (.branch 31 (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-22)))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (-34)) (.leaf (-33))) (.branch 21 (.leaf (-32)) (.leaf (-31)))) (.branch 24 (.branch 23 (.leaf (-30)) (.leaf (-29))) (.branch 25 (.leaf (-28)) (.leaf (-27))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-25))) (.branch 29 (.leaf (-24)) (.leaf (-23)))) (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))))) (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_311_6034 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (7)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (4)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (6)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (5)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (2)) (.branch 34 (.leaf (4)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (8)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (4)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (5)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (3)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (6)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_6034
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 32 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14))))) (.branch 45 (.branch 40 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17)))) (.branch 48 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20))))))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-20))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-6)) (.leaf (-7)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (-1))) (.branch 42 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 23 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-42))),
  (.branch 36 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 46 (.leaf (-9)) (.branch 49 (.leaf (-7)) (.leaf (-5)))),
  (.branch 48 (.branch 38 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 42 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.branch 48 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3))))),
  (.branch 44 (.branch 43 (.leaf (-3)) (.leaf (-2))) (.branch 45 (.leaf (-1)) (.leaf (0)))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 20 (.branch 15 (.branch 12 (.branch 11 (.leaf (-42)) (.leaf (-41))) (.branch 13 (.leaf (-40)) (.branch 14 (.leaf (-39)) (.leaf (-38))))) (.branch 17 (.branch 16 (.leaf (-37)) (.leaf (-36))) (.branch 18 (.leaf (-35)) (.branch 19 (.leaf (-34)) (.leaf (-33)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-32)) (.leaf (-31))) (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28))))) (.branch 28 (.branch 26 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25)))) (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-22))))))) (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_311_6035 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (8)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (4)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (7)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (8)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (6)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (7)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (3)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (8)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (6)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (7)) (.leaf (2))))))))
  code := certificateP9_6035
  counts := ![(.branch 23 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 49 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-43))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (-16)) (.leaf (-17)))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (-37))) (.branch 39 (.leaf (-38)) (.leaf (-39)))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (-28))) (.branch 42 (.leaf (-29)) (.leaf (-30))))]
  high := ![(.branch 50 (.leaf (-12)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 46 (.leaf (-8)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 44 (.branch 40 (.branch 4 (.leaf (-43)) (.branch 39 (.leaf (-42)) (.leaf (-39)))) (.branch 42 (.branch 41 (.leaf (-36)) (.leaf (-33))) (.branch 43 (.leaf (-30)) (.leaf (-27))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-24)) (.leaf (-21))) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 30 (.leaf (-17)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-39)) (.branch 41 (.leaf (-36)) (.leaf (-33)))) (.branch 43 (.leaf (-30)) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 17 (.leaf (-4)) (.leaf (-3))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-30)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))))]
def witnessP9_311_6036 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (6))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (1)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (7))) (.branch 25 (.leaf (2)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (5)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (4)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (6))) (.branch 38 (.leaf (0)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (2)))) (.branch 43 (.leaf (5)) (.branch 44 (.leaf (1)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (8))) (.branch 51 (.leaf (2)) (.leaf (1))))))))
  code := certificateP9_6036
  counts := ![(.branch 23 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 45 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 49 (.leaf (13)) (.leaf (14)))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 48 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 15 (.leaf (-24)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.branch 28 (.leaf (-11)) (.leaf (-16)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 46 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.leaf (-15))),
  (.branch 24 (.leaf (0)) (.leaf (-28))),
  (.branch 50 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 46 (.branch 42 (.leaf (-25)) (.leaf (-23))) (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-14)) (.leaf (-7))))),
  (.branch 41 (.branch 33 (.branch 29 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.leaf (-13)))) (.branch 49 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 50 (.leaf (-5)) (.leaf (0))))),
  (.branch 34 (.leaf (-5)) (.branch 43 (.leaf (-4)) (.leaf (-3)))),
  (.branch 49 (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3))))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 31 (.branch 27 (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26)))) (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.leaf (-22))))) (.branch 34 (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19)))) (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))))) (.branch 45 (.branch 41 (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_311_6037 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (4)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (7)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (3)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (1)) (.branch 28 (.leaf (0)) (.leaf (2)))) (.branch 30 (.leaf (4)) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (3)) (.branch 34 (.leaf (6)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (8)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (1)))) (.branch 43 (.leaf (4)) (.branch 44 (.leaf (0)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (7)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6037
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 46 (.leaf (9)) (.branch 50 (.leaf (10)) (.leaf (11)))))),
  (.branch 24 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-31))) (.branch 31 (.leaf (-35)) (.branch 39 (.leaf (-41)) (.leaf (-49))))),
  (.branch 2 (.leaf (0)) (.branch 50 (.leaf (-23)) (.leaf (-29)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-9))) (.branch 24 (.leaf (-11)) (.branch 29 (.leaf (-17)) (.leaf (-19))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (-14))) (.branch 25 (.leaf (-15)) (.leaf (-17)))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (-8))) (.branch 43 (.leaf (-12)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5))),
  (.branch 13 (.leaf (0)) (.branch 38 (.leaf (-13)) (.leaf (-14))))]
  high := ![(.branch 49 (.branch 40 (.leaf (-49)) (.leaf (-48))) (.branch 50 (.leaf (-39)) (.branch 51 (.leaf (-30)) (.leaf (-21))))),
  (.branch 51 (.leaf (-29)) (.leaf (-21))),
  (.branch 30 (.leaf (-19)) (.branch 46 (.leaf (-18)) (.leaf (-13)))),
  (.branch 42 (.branch 26 (.leaf (-17)) (.branch 34 (.leaf (-16)) (.leaf (-15)))) (.branch 50 (.leaf (-14)) (.branch 51 (.leaf (-11)) (.leaf (-8))))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))))),
  (.leaf (0)),
  (.branch 43 (.branch 38 (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 41 (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_311_6038 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (7)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (6)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (1)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (5)) (.leaf (8))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (4))))) (.branch 35 (.branch 33 (.leaf (6)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (2))) (.branch 38 (.leaf (0)) (.leaf (7)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (5)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (2)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (1)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (6)) (.leaf (8))))))))
  code := certificateP9_6038
  counts := ![(.branch 23 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 35 (.leaf (9)) (.leaf (10)))) (.branch 45 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 49 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 15 (.leaf (-16)) (.branch 41 (.leaf (-20)) (.leaf (-23))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 14 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 22 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 48 (.leaf (-14)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-4)) (.leaf (-5)))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 46 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-16)) (.leaf (-11))))),
  (.branch 49 (.branch 41 (.leaf (-11)) (.branch 48 (.leaf (-10)) (.leaf (-8)))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 31 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-13))) (.branch 51 (.leaf (-10)) (.leaf (-7)))),
  (.branch 48 (.branch 33 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 43 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 34 (.leaf (-5)) (.leaf (-3))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_311_6039 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (7)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (6)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (8)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (2)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (6))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (7)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (1)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (5)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (8)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (6))) (.branch 51 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_6039
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 17 (.leaf (-18)) (.branch 22 (.leaf (-19)) (.leaf (-20))))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 19 (.leaf (-7)) (.branch 45 (.leaf (-8)) (.leaf (-9))))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-23))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (-3)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 50 (.branch 45 (.leaf (-11)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 36 (.leaf (-7)) (.leaf (-5))),
  (.branch 48 (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7)))) (.branch 50 (.branch 49 (.leaf (-6)) (.leaf (-5))) (.branch 51 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 46 (.branch 43 (.branch 7 (.leaf (-23)) (.branch 25 (.leaf (-22)) (.leaf (-21)))) (.branch 44 (.leaf (-19)) (.branch 45 (.leaf (-17)) (.leaf (-15))))) (.branch 49 (.branch 47 (.leaf (-13)) (.branch 48 (.leaf (-11)) (.leaf (-9)))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 33 (.leaf (-6)) (.branch 51 (.leaf (-5)) (.leaf (-3)))),
  (.branch 43 (.branch 38 (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_311_6040 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (7))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (6))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (4)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (0))) (.branch 38 (.leaf (1)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (3)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (8))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6040
  counts := ![(.branch 24 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 31 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-16))) (.branch 12 (.leaf (-17)) (.branch 17 (.leaf (-18)) (.leaf (-19))))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-33))),
  (.branch 45 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 41 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 50 (.branch 44 (.leaf (-19)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 31 (.leaf (-6)) (.leaf (-5))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (-33)) (.leaf (-32))) (.branch 22 (.leaf (-31)) (.leaf (-30)))) (.branch 25 (.branch 24 (.leaf (-29)) (.leaf (-28))) (.branch 26 (.leaf (-27)) (.leaf (-26))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.leaf (-22)))) (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.leaf (-18)))))) (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_311_6041 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (7)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (3)) (.leaf (8))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (6))))) (.branch 35 (.branch 33 (.leaf (3)) (.branch 34 (.leaf (0)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (2))) (.branch 38 (.leaf (0)) (.leaf (7)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (3)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (4)) (.leaf (8))))))))
  code := certificateP9_6041
  counts := ![(.branch 23 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 46 (.branch 42 (.leaf (11)) (.leaf (12))) (.branch 49 (.leaf (13)) (.leaf (14)))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.leaf (7))))),
  (.branch 29 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-19)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-31))) (.branch 47 (.leaf (-34)) (.leaf (-35)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (-3))) (.branch 21 (.leaf (-6)) (.leaf (-9)))),
  (.branch 19 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 50 (.branch 35 (.leaf (-22)) (.leaf (-21))) (.branch 51 (.leaf (-14)) (.leaf (-7)))),
  (.branch 49 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 44 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 49 (.branch 48 (.leaf (-35)) (.leaf (-28))) (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-14)) (.leaf (-7))))),
  (.branch 22 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7)))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_311_6042 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (4)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (6)) (.branch 21 (.leaf (1)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (4)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (8))))) (.branch 35 (.branch 33 (.leaf (4)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (2))) (.branch 38 (.leaf (0)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (4)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (2)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (6)) (.branch 47 (.leaf (1)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (4)) (.leaf (5))))))))
  code := certificateP9_6042
  counts := ![(.branch 23 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 35 (.leaf (9)) (.leaf (10)))) (.branch 45 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 49 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 15 (.leaf (-16)) (.branch 41 (.leaf (-20)) (.leaf (-23))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 14 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 22 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 48 (.leaf (-14)) (.leaf (-16)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 20 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-46))),
  (.branch 32 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 46 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-16)) (.leaf (-11))))),
  (.branch 49 (.branch 41 (.leaf (-11)) (.branch 48 (.leaf (-10)) (.leaf (-8)))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 31 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-13))) (.branch 51 (.leaf (-10)) (.leaf (-7)))),
  (.branch 34 (.leaf (-5)) (.branch 43 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 17 (.branch 11 (.branch 8 (.branch 7 (.leaf (-46)) (.leaf (-45))) (.branch 9 (.leaf (-44)) (.branch 10 (.leaf (-43)) (.leaf (-42))))) (.branch 14 (.branch 12 (.leaf (-41)) (.branch 13 (.leaf (-40)) (.leaf (-39)))) (.branch 15 (.leaf (-38)) (.branch 16 (.leaf (-37)) (.leaf (-36)))))) (.branch 23 (.branch 20 (.branch 18 (.leaf (-35)) (.branch 19 (.leaf (-34)) (.leaf (-33)))) (.branch 21 (.leaf (-32)) (.branch 22 (.leaf (-31)) (.leaf (-30))))) (.branch 26 (.branch 24 (.leaf (-29)) (.branch 25 (.leaf (-28)) (.leaf (-27)))) (.branch 27 (.leaf (-26)) (.branch 28 (.leaf (-25)) (.leaf (-24))))))) (.branch 40 (.branch 34 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_311_6043 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (7)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (2)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (4)) (.leaf (8))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 30 (.leaf (5)) (.branch 31 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (6)) (.leaf (4)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (1)) (.leaf (7)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (5)) (.leaf (2)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (6)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (5)) (.leaf (8))))))))
  code := certificateP9_6043
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 17 (.leaf (-18)) (.branch 22 (.leaf (-19)) (.leaf (-20))))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (-3)) (.leaf (-4)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 19 (.leaf (-7)) (.branch 45 (.leaf (-8)) (.leaf (-9))))),
  (.branch 4 (.leaf (0)) (.branch 35 (.leaf (-32)) (.leaf (-33)))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 50 (.branch 45 (.leaf (-11)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 51 (.leaf (-4)) (.leaf (-3))),
  (.branch 48 (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7)))) (.branch 50 (.branch 49 (.leaf (-6)) (.leaf (-5))) (.branch 51 (.leaf (-4)) (.leaf (-3))))),
  (.branch 48 (.branch 36 (.leaf (-33)) (.branch 47 (.leaf (-30)) (.leaf (-25)))) (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 10 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_311_6044 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (5)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (8)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (4)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 30 (.leaf (4)) (.branch 31 (.leaf (1)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (6)) (.branch 34 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (5)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (3)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (7)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (4)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_6044
  counts := ![(.branch 24 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 43 (.leaf (7)) (.branch 49 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 46 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 44 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 27 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-34))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-14)) (.leaf (-15)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 44 (.leaf (0)) (.leaf (-8))),
  (.branch 18 (.leaf (0)) (.leaf (-34)))]
  high := ![(.branch 37 (.branch 28 (.leaf (-19)) (.leaf (-18))) (.branch 46 (.leaf (-17)) (.branch 51 (.leaf (-14)) (.leaf (-9))))),
  (.branch 38 (.branch 3 (.leaf (-34)) (.branch 32 (.leaf (-33)) (.leaf (-31)))) (.branch 50 (.branch 44 (.leaf (-29)) (.leaf (-27))) (.branch 51 (.leaf (-18)) (.leaf (-9))))),
  (.branch 35 (.branch 29 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.branch 47 (.leaf (-2)) (.leaf (0))))),
  (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-1)),
  (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (-34)) (.leaf (-33))) (.branch 21 (.leaf (-32)) (.leaf (-31)))) (.branch 24 (.branch 23 (.leaf (-30)) (.leaf (-29))) (.branch 25 (.leaf (-28)) (.leaf (-27))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-25))) (.branch 29 (.leaf (-24)) (.leaf (-23)))) (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))))) (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_311_6045 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (6)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (5)) (.branch 15 (.leaf (1)) (.leaf (4)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (5))) (.branch 25 (.leaf (4)) (.leaf (7))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 30 (.leaf (6)) (.branch 31 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (4)) (.branch 34 (.leaf (1)) (.leaf (5)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (0))) (.branch 38 (.leaf (3)) (.leaf (8)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (6)) (.branch 41 (.leaf (1)) (.leaf (4)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (5))))) (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (6))) (.branch 51 (.leaf (4)) (.leaf (7))))))))
  code := certificateP9_6045
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 45 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-21))) (.branch 11 (.leaf (-22)) (.leaf (-23)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-2)) (.leaf (-4)))) (.branch 36 (.leaf (-5)) (.branch 49 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (-32))) (.branch 24 (.leaf (-34)) (.leaf (-36)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (-7))) (.branch 50 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 49 (.branch 38 (.leaf (-23)) (.leaf (-20))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.leaf (-5)) (.branch 43 (.leaf (-4)) (.leaf (-3)))),
  (.branch 48 (.branch 46 (.branch 25 (.leaf (-36)) (.leaf (-35))) (.branch 47 (.leaf (-30)) (.leaf (-25)))) (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 51 (.leaf (-10)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_311_6046 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (4)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (8)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (5)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 30 (.leaf (6)) (.branch 31 (.leaf (1)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (7)) (.branch 34 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (4)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (3)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (8)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (6)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_6046
  counts := ![(.branch 24 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 43 (.leaf (7)) (.branch 49 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 46 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 27 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-34))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-40)) (.leaf (-41)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (-13))) (.branch 47 (.leaf (-14)) (.leaf (-15)))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 18 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 37 (.branch 28 (.leaf (-19)) (.leaf (-18))) (.branch 46 (.leaf (-17)) (.branch 51 (.leaf (-14)) (.leaf (-9))))),
  (.branch 38 (.branch 3 (.leaf (-34)) (.branch 32 (.leaf (-33)) (.leaf (-31)))) (.branch 50 (.branch 44 (.leaf (-29)) (.leaf (-27))) (.branch 51 (.leaf (-18)) (.leaf (-9))))),
  (.branch 35 (.branch 29 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.branch 47 (.leaf (-2)) (.leaf (0))))),
  (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1)),
  (.branch 45 (.branch 41 (.branch 22 (.leaf (-41)) (.branch 40 (.leaf (-39)) (.leaf (-36)))) (.branch 43 (.branch 42 (.leaf (-33)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_311_6047 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 17 (.leaf (6)) (.branch 18 (.leaf (1)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (7)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (2)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 30 (.leaf (8)) (.branch 31 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (6)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (4))) (.branch 38 (.leaf (1)) (.leaf (7)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (3)))) (.branch 43 (.leaf (5)) (.branch 44 (.leaf (1)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (8)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (4))) (.branch 51 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_6047
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 31 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 22 (.branch 1 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-9)))) (.branch 35 (.leaf (-10)) (.branch 48 (.leaf (-11)) (.leaf (-12))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-16))) (.branch 12 (.leaf (-17)) (.leaf (-18)))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))) (.branch 20 (.leaf (-3)) (.branch 25 (.leaf (-4)) (.leaf (-5))))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-28))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-40)) (.leaf (-41)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (-13))) (.branch 47 (.leaf (-14)) (.leaf (-15))))]
  high := ![(.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-10))) (.branch 51 (.leaf (-8)) (.leaf (-6)))),
  (.branch 50 (.branch 39 (.leaf (-18)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (-5)),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.branch 44 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 35 (.leaf (-2)) (.leaf (0))),
  (.branch 45 (.branch 41 (.branch 22 (.leaf (-41)) (.branch 40 (.leaf (-39)) (.leaf (-36)))) (.branch 43 (.branch 42 (.leaf (-33)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_311_6048 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (8)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (5))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (6)) (.leaf (2)))) (.branch 17 (.leaf (7)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (3)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (1)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 30 (.leaf (8)) (.branch 31 (.leaf (1)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (4)) (.branch 34 (.leaf (2)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (5))) (.branch 38 (.leaf (3)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (6)) (.leaf (1)))) (.branch 43 (.leaf (7)) (.branch 44 (.leaf (0)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (3)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_6048
  counts := ![(.branch 23 (.branch 9 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 48 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 45 (.leaf (7)) (.branch 51 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 35 (.leaf (-21)) (.leaf (-23)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-34))) (.branch 36 (.leaf (-39)) (.leaf (-40)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 26 (.leaf (0)) (.leaf (-2))),
  (.branch 17 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-22)))]
  high := ![(.branch 45 (.branch 36 (.leaf (-23)) (.leaf (-22))) (.branch 50 (.leaf (-19)) (.branch 51 (.leaf (-14)) (.leaf (-9))))),
  (.branch 49 (.branch 37 (.leaf (-40)) (.branch 43 (.leaf (-38)) (.leaf (-36)))) (.branch 50 (.leaf (-27)) (.branch 51 (.leaf (-18)) (.leaf (-9))))),
  (.branch 40 (.branch 11 (.leaf (-14)) (.leaf (-13))) (.branch 46 (.leaf (-11)) (.leaf (-9)))),
  (.branch 48 (.branch 30 (.leaf (-17)) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 27 (.leaf (-2)) (.branch 42 (.leaf (-1)) (.leaf (0)))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.branch 35 (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))) (.branch 38 (.branch 36 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_311_6049 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (8)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (6)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (7)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (8)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (1)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 30 (.leaf (7)) (.branch 31 (.leaf (1)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (4)) (.branch 34 (.leaf (2)) (.leaf (6)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (8)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (3)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (7)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (6))) (.branch 51 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6049
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 43 (.leaf (7)) (.branch 48 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 45 (.leaf (7)) (.branch 51 (.leaf (8)) (.leaf (9)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 44 (.leaf (-20)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-34)) (.leaf (-37)))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 45 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.branch 35 (.leaf (-5)) (.leaf (-7)))),
  (.branch 12 (.leaf (0)) (.leaf (-16))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (-40))) (.branch 38 (.leaf (-41)) (.leaf (-42))))]
  high := ![(.branch 50 (.branch 45 (.leaf (-22)) (.leaf (-19))) (.branch 51 (.leaf (-14)) (.leaf (-9)))),
  (.branch 49 (.branch 20 (.leaf (-37)) (.leaf (-36))) (.branch 50 (.leaf (-27)) (.branch 51 (.leaf (-18)) (.leaf (-9))))),
  (.branch 46 (.leaf (-11)) (.leaf (-9))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 36 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))),
  (.branch 49 (.branch 13 (.leaf (-16)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 45 (.branch 41 (.branch 39 (.leaf (-42)) (.branch 40 (.leaf (-39)) (.leaf (-36)))) (.branch 43 (.branch 42 (.leaf (-33)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))))]
def witnessP9_311_6050 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (5))) (.branch 12 (.leaf (4)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (7))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (5))) (.branch 25 (.leaf (3)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (6))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (3)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (5))) (.branch 38 (.leaf (4)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (3)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (8))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (4)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (5))) (.branch 51 (.leaf (3)) (.leaf (2))))))))
  code := certificateP9_6050
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 31 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-10)))) (.branch 30 (.leaf (-11)) (.branch 43 (.leaf (-12)) (.leaf (-13))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.branch 20 (.leaf (-3)) (.leaf (-4))))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-33))),
  (.branch 45 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 49 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-10)) (.branch 51 (.leaf (-8)) (.leaf (-6))))),
  (.branch 50 (.branch 34 (.leaf (-17)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 47 (.leaf (-4)) (.leaf (0))),
  (.branch 43 (.leaf (-4)) (.leaf (-3))),
  (.branch 48 (.branch 30 (.leaf (-17)) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (-33)) (.leaf (-32))) (.branch 22 (.leaf (-31)) (.leaf (-30)))) (.branch 25 (.branch 24 (.leaf (-29)) (.leaf (-28))) (.branch 26 (.leaf (-27)) (.leaf (-26))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.leaf (-22)))) (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.leaf (-18)))))) (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_311_6051 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (8)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (7)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (2)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (1)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (4)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (8)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (3)) (.branch 34 (.leaf (0)) (.leaf (5)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (4))) (.branch 38 (.leaf (0)) (.leaf (6)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (3)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (7)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (1)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_6051
  counts := ![(.branch 23 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 45 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 49 (.leaf (13)) (.leaf (14)))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 15 (.leaf (-24)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.leaf (-38))),
  (.branch 6 (.leaf (0)) (.branch 28 (.leaf (-10)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-19)))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 18 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-21)))]
  high := ![(.branch 46 (.branch 42 (.leaf (-25)) (.leaf (-23))) (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-14)) (.leaf (-7))))),
  (.branch 48 (.branch 18 (.branch 3 (.leaf (-38)) (.leaf (-37))) (.branch 33 (.leaf (-36)) (.leaf (-35)))) (.branch 50 (.branch 49 (.leaf (-28)) (.leaf (-21))) (.branch 51 (.leaf (-14)) (.leaf (-7))))),
  (.branch 29 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-7)))),
  (.branch 51 (.leaf (-6)) (.leaf (-3))),
  (.branch 48 (.branch 38 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_311_6052 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (4)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (4)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (7))) (.branch 25 (.leaf (2)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (3))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (4)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (8))) (.branch 38 (.leaf (1)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (4)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (4)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_6052
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 50 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 17 (.leaf (-18)) (.branch 22 (.leaf (-19)) (.leaf (-20))))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-4)) (.leaf (-6)))) (.branch 34 (.leaf (-7)) (.branch 47 (.leaf (-8)) (.leaf (-9))))),
  (.branch 50 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-41))),
  (.branch 24 (.leaf (0)) (.leaf (-28))),
  (.branch 37 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 50 (.branch 45 (.leaf (-11)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 36 (.leaf (-7)) (.leaf (-5))),
  (.branch 46 (.leaf (-1)) (.leaf (0))),
  (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 31 (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-41)) (.leaf (-40))) (.branch 14 (.leaf (-39)) (.branch 15 (.leaf (-38)) (.leaf (-37))))) (.branch 18 (.branch 17 (.leaf (-36)) (.leaf (-35))) (.branch 19 (.leaf (-34)) (.branch 20 (.leaf (-33)) (.leaf (-32)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-31)) (.leaf (-30))) (.branch 24 (.leaf (-29)) (.branch 25 (.leaf (-28)) (.leaf (-27))))) (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-25))) (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-22))))))) (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 38 (.branch 31 (.branch 27 (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26)))) (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.leaf (-22))))) (.branch 34 (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19)))) (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))))) (.branch 45 (.branch 41 (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_311_6053 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (7))) (.branch 12 (.leaf (4)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (5)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (6))) (.branch 25 (.leaf (5)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (3))))) (.branch 35 (.branch 33 (.leaf (5)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (8))) (.branch 38 (.leaf (4)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (5)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (6))) (.branch 51 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_6053
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 24 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-41))),
  (.branch 37 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 46 (.leaf (-1)) (.leaf (0))),
  (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.leaf (-5)) (.branch 43 (.leaf (-4)) (.leaf (-3)))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 31 (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-41)) (.leaf (-40))) (.branch 14 (.leaf (-39)) (.branch 15 (.leaf (-38)) (.leaf (-37))))) (.branch 18 (.branch 17 (.leaf (-36)) (.leaf (-35))) (.branch 19 (.leaf (-34)) (.branch 20 (.leaf (-33)) (.leaf (-32)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-31)) (.leaf (-30))) (.branch 24 (.leaf (-29)) (.branch 25 (.leaf (-28)) (.leaf (-27))))) (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-25))) (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-22))))))) (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_311_6054 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (8)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (0)) (.leaf (4)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (5)) (.leaf (8))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (7)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (1)) (.branch 28 (.leaf (0)) (.leaf (4)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (1)) (.leaf (5))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (8)) (.leaf (7)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (3))) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (6)) (.branch 41 (.leaf (1)) (.leaf (4)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (5)) (.leaf (8))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (7)) (.leaf (3))) (.branch 51 (.leaf (1)) (.leaf (6))))))))
  code := certificateP9_6054
  counts := ![(.branch 25 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 43 (.leaf (9)) (.branch 48 (.leaf (10)) (.leaf (11)))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 46 (.leaf (9)) (.branch 51 (.leaf (10)) (.leaf (11)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 28 (.leaf (-23)) (.leaf (-28)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (-6))) (.branch 45 (.leaf (-9)) (.leaf (-11))))]
  high := ![(.branch 44 (.branch 34 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 50 (.branch 49 (.leaf (-24)) (.leaf (-19))) (.branch 51 (.leaf (-14)) (.leaf (-9))))),
  (.branch 37 (.branch 3 (.leaf (-14)) (.branch 32 (.leaf (-13)) (.leaf (-12)))) (.branch 42 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-9))))),
  (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 50 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 48 (.branch 46 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-9)))) (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))))]
def witnessP9_311_6055 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (4)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (0)) (.leaf (8)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (0)) (.leaf (6))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (7)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (0))) (.branch 38 (.leaf (1)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (3)) (.leaf (4)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (6))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (8)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (5))))))))
  code := certificateP9_6055
  counts := ![(.branch 24 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 31 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-16))) (.branch 12 (.leaf (-17)) (.branch 17 (.leaf (-18)) (.leaf (-19))))),
  (.branch 4 (.leaf (0)) (.leaf (-32))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (-2))) (.branch 30 (.leaf (-4)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 41 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 50 (.branch 44 (.leaf (-19)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 48 (.branch 26 (.branch 5 (.leaf (-32)) (.leaf (-31))) (.branch 47 (.leaf (-30)) (.leaf (-25)))) (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 31 (.leaf (-6)) (.leaf (-5))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_311_6056 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (3)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (4)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 17 (.leaf (6)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (8)) (.branch 21 (.leaf (4)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (0)) (.leaf (6))))) (.branch 35 (.branch 33 (.leaf (7)) (.branch 34 (.leaf (2)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (4)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (1)))) (.branch 43 (.leaf (6)) (.branch 44 (.leaf (3)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (8)) (.branch 47 (.leaf (4)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_6056
  counts := ![(.branch 24 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 27 (.leaf (-8)) (.branch 31 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.branch 28 (.leaf (-14)) (.leaf (-16)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 18 (.leaf (-8)) (.branch 40 (.leaf (-9)) (.leaf (-10))))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-8))) (.branch 43 (.leaf (-11)) (.leaf (-13)))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 46 (.branch 32 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-8)) (.leaf (-6)))),
  (.branch 43 (.branch 29 (.leaf (-16)) (.branch 36 (.leaf (-15)) (.leaf (-14)))) (.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-10)) (.leaf (-7))))),
  (.branch 49 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-5)) (.leaf (-3))))),
  (.branch 45 (.leaf (-2)) (.leaf (0))),
  (.branch 48 (.branch 30 (.leaf (-17)) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-1)),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))))),
  (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_311_6057 : CycleWitness 9 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (7)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (6)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (4))) (.branch 25 (.leaf (3)) (.leaf (8))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (5)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (6)) (.branch 34 (.leaf (1)) (.leaf (4)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (0))) (.branch 38 (.leaf (3)) (.leaf (7)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (5)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 46 (.leaf (6)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (5))) (.branch 51 (.leaf (3)) (.leaf (8))))))))
  code := certificateP9_6057
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 42 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 45 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-21))) (.branch 11 (.leaf (-22)) (.branch 16 (.leaf (-23)) (.leaf (-24))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-37))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (-7))) (.branch 29 (.leaf (-9)) (.leaf (-11)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 49 (.branch 43 (.leaf (-24)) (.leaf (-20))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5))))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 45 (.leaf (-3)) (.leaf (-2))),
  (.branch 47 (.branch 25 (.branch 4 (.leaf (-37)) (.leaf (-36))) (.branch 46 (.leaf (-35)) (.leaf (-30)))) (.branch 49 (.branch 48 (.leaf (-25)) (.leaf (-20))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 30 (.leaf (-11)) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_311 : Fin 57 → CycleWitness 9 := ![witnessP9_311_6001, witnessP9_311_6002, witnessP9_311_6003, witnessP9_311_6004, witnessP9_311_6005, witnessP9_311_6006, witnessP9_311_6007, witnessP9_311_6008, witnessP9_311_6009, witnessP9_311_6010, witnessP9_311_6011, witnessP9_311_6012, witnessP9_311_6013, witnessP9_311_6014, witnessP9_311_6015, witnessP9_311_6016, witnessP9_311_6017, witnessP9_311_6018, witnessP9_311_6019, witnessP9_311_6020, witnessP9_311_6021, witnessP9_311_6022, witnessP9_311_6023, witnessP9_311_6024, witnessP9_311_6025, witnessP9_311_6026, witnessP9_311_6027, witnessP9_311_6028, witnessP9_311_6029, witnessP9_311_6030, witnessP9_311_6031, witnessP9_311_6032, witnessP9_311_6033, witnessP9_311_6034, witnessP9_311_6035, witnessP9_311_6036, witnessP9_311_6037, witnessP9_311_6038, witnessP9_311_6039, witnessP9_311_6040, witnessP9_311_6041, witnessP9_311_6042, witnessP9_311_6043, witnessP9_311_6044, witnessP9_311_6045, witnessP9_311_6046, witnessP9_311_6047, witnessP9_311_6048, witnessP9_311_6049, witnessP9_311_6050, witnessP9_311_6051, witnessP9_311_6052, witnessP9_311_6053, witnessP9_311_6054, witnessP9_311_6055, witnessP9_311_6056, witnessP9_311_6057]
end RealPinwheel.FiveSixths


