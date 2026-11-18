-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_001
-- name    : RealPinwheel_FiveSixths_WitnessD6_001
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:01:24.596201+00:00
-- url     : https://prove2.me/theorems/15f76771-b597-4271-b6ea-fb2bc0e220eb
-- title:
--   Exact witness block D6_001
-- statement:
--   These exact witnesses represent words 17 through 35 of source certificate file D6. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D6, entries 17–35; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D6.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD6
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD6_001_16 : CycleWitness 6 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (4))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (5)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (3)) (.leaf (0))) (.branch 41 (.leaf (1)) (.leaf (2)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (4)) (.leaf (0))) (.branch 48 (.leaf (1)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (2)) (.branch 51 (.leaf (1)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (5))))))))
  code := certificateD6_16
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 24 (.leaf (10)) (.leaf (11)))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (12)) (.branch 31 (.leaf (13)) (.leaf (14)))) (.branch 35 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17))))) (.branch 47 (.branch 43 (.leaf (18)) (.branch 45 (.leaf (19)) (.leaf (20)))) (.branch 52 (.branch 49 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24))))))),
  (.branch 27 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 55 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.branch 7 (.leaf (-6)) (.leaf (-7))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 50 (.leaf (-13)) (.leaf (-14)))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 50 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-3)))),
  (.branch 52 (.leaf (-3)) (.leaf (-2))),
  (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-12)) (.leaf (-10)))) (.branch 54 (.leaf (-8)) (.branch 55 (.leaf (-6)) (.leaf (-4))))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 51 (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 52 (.leaf (-6)) (.leaf (-5))) (.branch 54 (.leaf (-4)) (.branch 55 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 37 (.leaf (-2)) (.branch 38 (.leaf (-1)) (.leaf (0))))]
def witnessD6_001_17 : CycleWitness 6 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (4)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 26 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2))))))) (.branch 42 (.branch 34 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (0)) (.leaf (1))))) (.branch 37 (.branch 35 (.leaf (3)) (.branch 36 (.leaf (0)) (.leaf (2)))) (.branch 40 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (2)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (1))))) (.branch 51 (.branch 49 (.leaf (5)) (.branch 50 (.leaf (0)) (.leaf (2)))) (.branch 54 (.branch 52 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2))))))))
  code := certificateD6_17
  counts := ![(.branch 27 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 22 (.leaf (9)) (.branch 24 (.leaf (10)) (.leaf (11)))))) (.branch 41 (.branch 33 (.branch 29 (.leaf (12)) (.branch 31 (.leaf (13)) (.leaf (14)))) (.branch 36 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17))))) (.branch 47 (.branch 43 (.leaf (18)) (.branch 45 (.leaf (19)) (.leaf (20)))) (.branch 52 (.branch 50 (.leaf (21)) (.leaf (22))) (.branch 55 (.leaf (23)) (.leaf (24))))))),
  (.branch 26 (.branch 12 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 54 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 7 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 26 (.branch 2 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))) (.branch 40 (.leaf (-6)) (.branch 54 (.leaf (-8)) (.leaf (-10))))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 21 (.leaf (0)) (.leaf (-35))),
  (.branch 49 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 48 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-3)))),
  (.branch 55 (.leaf (-10)) (.leaf (-9))),
  (.branch 47 (.leaf (-2)) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.branch 45 (.branch 40 (.branch 37 (.branch 36 (.leaf (-21)) (.leaf (-20))) (.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-18)) (.leaf (-17))))) (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 29 (.branch 25 (.branch 23 (.branch 22 (.leaf (-35)) (.leaf (-34))) (.branch 24 (.leaf (-33)) (.leaf (-32)))) (.branch 27 (.branch 26 (.leaf (-31)) (.leaf (-30))) (.branch 28 (.leaf (-29)) (.leaf (-28))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-27)) (.leaf (-26))) (.branch 32 (.leaf (-25)) (.leaf (-24)))) (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))))) (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_001_18 : CycleWitness 6 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (3)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (4))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (0))) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (0)) (.leaf (3)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (4)) (.leaf (0))) (.branch 48 (.leaf (2)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (1)) (.branch 51 (.leaf (0)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (5))))))))
  code := certificateD6_18
  counts := ![(.branch 27 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 15 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))) (.branch 23 (.branch 21 (.leaf (10)) (.leaf (11))) (.branch 25 (.leaf (12)) (.leaf (13)))))) (.branch 41 (.branch 33 (.branch 29 (.leaf (14)) (.branch 31 (.leaf (15)) (.leaf (16)))) (.branch 37 (.branch 35 (.leaf (17)) (.leaf (18))) (.branch 39 (.leaf (19)) (.leaf (20))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 47 (.leaf (23)) (.leaf (24)))) (.branch 53 (.branch 51 (.leaf (25)) (.leaf (26))) (.branch 55 (.leaf (27)) (.leaf (28))))))),
  (.branch 22 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.branch 32 (.leaf (-11)) (.leaf (-12)))),
  (.branch 28 (.branch 10 (.leaf (0)) (.leaf (-9))) (.branch 46 (.leaf (-10)) (.leaf (-11)))),
  (.branch 18 (.leaf (0)) (.leaf (-1)))]
  high := ![(.leaf (-1)),
  (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 53 (.branch 33 (.leaf (-12)) (.branch 43 (.leaf (-11)) (.leaf (-10)))) (.branch 54 (.leaf (-8)) (.branch 55 (.leaf (-6)) (.leaf (-4))))),
  (.branch 51 (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 52 (.leaf (-6)) (.leaf (-5))) (.branch 54 (.leaf (-4)) (.branch 55 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 19 (.leaf (-1)) (.leaf (0)))]
def witnessD6_001_19 : CycleWitness 6 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (5)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (4)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (4)) (.leaf (1))) (.branch 46 (.leaf (0)) (.leaf (3))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (2)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (5)) (.leaf (2))))))))
  code := certificateD6_19
  counts := ![(.branch 25 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 23 (.leaf (10)) (.leaf (11)))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (12)) (.branch 30 (.leaf (13)) (.leaf (14)))) (.branch 34 (.leaf (15)) (.branch 37 (.leaf (16)) (.leaf (17))))) (.branch 46 (.branch 41 (.leaf (18)) (.branch 43 (.leaf (19)) (.leaf (20)))) (.branch 50 (.branch 48 (.leaf (21)) (.leaf (22))) (.branch 52 (.leaf (23)) (.leaf (24))))))),
  (.branch 24 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.branch 7 (.leaf (-7)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-3)) (.branch 42 (.leaf (-5)) (.leaf (-6))))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (-9)) (.leaf (-10)))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 53 (.leaf (-8)) (.leaf (-4))),
  (.branch 52 (.branch 46 (.leaf (-18)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.branch 51 (.branch 43 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 48 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_001_20 : CycleWitness 6 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (0))) (.branch 26 (.leaf (3)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (3)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (4))) (.branch 46 (.leaf (0)) (.leaf (3))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (0))) (.branch 53 (.leaf (3)) (.leaf (5))))))))
  code := certificateD6_20
  counts := ![(.branch 25 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 23 (.leaf (10)) (.leaf (11)))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (12)) (.branch 30 (.leaf (13)) (.leaf (14)))) (.branch 34 (.leaf (15)) (.branch 37 (.leaf (16)) (.leaf (17))))) (.branch 46 (.branch 41 (.leaf (18)) (.branch 43 (.leaf (19)) (.leaf (20)))) (.branch 50 (.branch 48 (.leaf (21)) (.leaf (22))) (.branch 52 (.leaf (23)) (.leaf (24))))))),
  (.branch 22 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.branch 7 (.leaf (-7)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-19)) (.leaf (-22)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-11)) (.leaf (-13)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 53 (.leaf (-8)) (.leaf (-4))),
  (.branch 50 (.branch 36 (.leaf (-22)) (.branch 43 (.leaf (-21)) (.leaf (-20)))) (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-12))) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 52 (.branch 45 (.leaf (-13)) (.leaf (-12))) (.branch 53 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-4)),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_001_21 : CycleWitness 6 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (2))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 44 (.leaf (1)) (.branch 45 (.leaf (0)) (.leaf (2))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (5)) (.leaf (0)))) (.branch 50 (.leaf (1)) (.branch 51 (.leaf (0)) (.leaf (2))))))))
  code := certificateD6_21
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 17 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))) (.branch 21 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 23 (.leaf (12)) (.leaf (13)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (14)) (.branch 28 (.leaf (15)) (.leaf (16)))) (.branch 34 (.branch 32 (.leaf (17)) (.leaf (18))) (.branch 36 (.leaf (19)) (.leaf (20))))) (.branch 45 (.branch 41 (.branch 40 (.leaf (21)) (.leaf (22))) (.branch 43 (.leaf (23)) (.leaf (24)))) (.branch 49 (.branch 47 (.leaf (25)) (.leaf (26))) (.branch 51 (.leaf (27)) (.leaf (28))))))),
  (.branch 24 (.branch 11 (.branch 3 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 29 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-5)))) (.branch 31 (.leaf (-7)) (.branch 44 (.leaf (-9)) (.leaf (-11))))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-30))),
  (.branch 48 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 46 (.branch 42 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))),
  (.branch 45 (.leaf (-11)) (.branch 51 (.leaf (-10)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 29 (.branch 25 (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))) (.branch 27 (.branch 26 (.leaf (-27)) (.leaf (-26))) (.branch 28 (.leaf (-25)) (.leaf (-24))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.leaf (-20)))) (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_001_22 : CycleWitness 6 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (0))) (.branch 23 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (2))))))) (.branch 39 (.branch 33 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (0))) (.branch 36 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 46 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (0))))) (.branch 48 (.branch 47 (.leaf (5)) (.leaf (0))) (.branch 49 (.leaf (1)) (.branch 51 (.leaf (0)) (.leaf (2))))))))
  code := certificateD6_22
  counts := ![(.branch 25 (.branch 12 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (8)) (.leaf (9))) (.branch 17 (.leaf (10)) (.leaf (11)))) (.branch 22 (.branch 20 (.leaf (12)) (.leaf (13))) (.branch 24 (.leaf (14)) (.leaf (15)))))) (.branch 38 (.branch 32 (.branch 28 (.branch 27 (.leaf (16)) (.leaf (17))) (.branch 30 (.leaf (18)) (.leaf (19)))) (.branch 35 (.branch 33 (.leaf (20)) (.leaf (21))) (.branch 37 (.leaf (22)) (.leaf (23))))) (.branch 45 (.branch 41 (.branch 40 (.leaf (24)) (.leaf (25))) (.branch 43 (.leaf (26)) (.leaf (27)))) (.branch 48 (.branch 46 (.leaf (28)) (.leaf (29))) (.branch 50 (.leaf (30)) (.branch 51 (.leaf (31)) (.leaf (32)))))))),
  (.branch 23 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-3)) (.branch 44 (.leaf (-4)) (.leaf (-5))))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-31))),
  (.branch 47 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 42 (.leaf (-10)) (.branch 47 (.leaf (-9)) (.leaf (-8)))),
  (.branch 50 (.branch 43 (.leaf (-7)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 47 (.branch 45 (.leaf (-5)) (.branch 46 (.leaf (-4)) (.leaf (-3)))) (.branch 48 (.leaf (-2)) (.branch 49 (.leaf (-1)) (.leaf (0))))),
  (.branch 43 (.branch 38 (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 28 (.branch 24 (.branch 22 (.leaf (-31)) (.branch 23 (.leaf (-30)) (.leaf (-29)))) (.branch 26 (.branch 25 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.leaf (-25))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-24)) (.leaf (-23))) (.branch 31 (.leaf (-22)) (.leaf (-21)))) (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-17)))))) (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_001_23 : CycleWitness 6 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (4))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (1)))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1)))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (5))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (2)) (.leaf (1)))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2))))))))
  code := certificateD6_23
  counts := ![(.branch 24 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 37 (.branch 28 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 31 (.leaf (12)) (.branch 34 (.leaf (13)) (.leaf (14))))) (.branch 44 (.branch 40 (.leaf (15)) (.branch 41 (.leaf (16)) (.leaf (17)))) (.branch 47 (.leaf (18)) (.branch 50 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.branch 51 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 7 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 46 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))) (.branch 28 (.leaf (-17)) (.branch 41 (.leaf (-20)) (.leaf (-23))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))) (.branch 38 (.branch 25 (.leaf (-4)) (.leaf (-5))) (.branch 51 (.leaf (-6)) (.leaf (-7))))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-32))),
  (.branch 46 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 45 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 48 (.leaf (-21)) (.branch 51 (.leaf (-20)) (.leaf (-16))))),
  (.leaf (-7)),
  (.branch 44 (.leaf (-1)) (.leaf (0))),
  (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 28 (.branch 24 (.branch 22 (.branch 21 (.leaf (-32)) (.leaf (-31))) (.branch 23 (.leaf (-30)) (.leaf (-29)))) (.branch 26 (.branch 25 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.leaf (-25))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-24)) (.leaf (-23))) (.branch 31 (.leaf (-22)) (.leaf (-21)))) (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-17)))))) (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_001_24 : CycleWitness 6 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (3)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (2)) (.leaf (1)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (5)))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (3)))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (1))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (5))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3)))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (1)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (4)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (3)))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (5)) (.leaf (1))))))))
  code := certificateD6_24
  counts := ![(.branch 24 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 37 (.branch 28 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 31 (.leaf (12)) (.branch 34 (.leaf (13)) (.leaf (14))))) (.branch 44 (.branch 40 (.leaf (15)) (.branch 41 (.leaf (16)) (.leaf (17)))) (.branch 47 (.leaf (18)) (.branch 50 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.branch 52 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))) (.branch 28 (.leaf (-17)) (.branch 41 (.leaf (-20)) (.leaf (-23))))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 20 (.leaf (-6)) (.branch 46 (.leaf (-7)) (.leaf (-8))))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 17 (.leaf (0)) (.branch 33 (.leaf (-1)) (.leaf (-4))))]
  high := ![(.branch 45 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 48 (.leaf (-21)) (.branch 51 (.leaf (-20)) (.leaf (-16))))),
  (.branch 49 (.leaf (-3)) (.leaf (0))),
  (.branch 49 (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 26 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 44 (.leaf (-19)) (.branch 45 (.leaf (-17)) (.leaf (-15))))) (.branch 49 (.branch 47 (.leaf (-13)) (.branch 48 (.leaf (-11)) (.leaf (-9)))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 34 (.leaf (-4)) (.leaf (-3)))]
def witnessD6_001_25 : CycleWitness 6 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (0)))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (4))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (5)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (4)) (.leaf (0)))) (.branch 44 (.leaf (1)) (.branch 45 (.leaf (0)) (.leaf (3))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (2)) (.leaf (0)))) (.branch 50 (.leaf (1)) (.branch 51 (.leaf (0)) (.leaf (5))))))))
  code := certificateD6_25
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 17 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))) (.branch 21 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 23 (.leaf (12)) (.leaf (13)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (14)) (.branch 28 (.leaf (15)) (.leaf (16)))) (.branch 34 (.branch 32 (.leaf (17)) (.leaf (18))) (.branch 36 (.leaf (19)) (.leaf (20))))) (.branch 45 (.branch 41 (.branch 40 (.leaf (21)) (.leaf (22))) (.branch 43 (.leaf (23)) (.leaf (24)))) (.branch 49 (.branch 47 (.leaf (25)) (.leaf (26))) (.branch 51 (.leaf (27)) (.leaf (28))))))),
  (.branch 24 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-6)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (-9))) (.branch 42 (.leaf (-10)) (.leaf (-12)))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 46 (.branch 42 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))),
  (.branch 51 (.leaf (-4)) (.leaf (-2))),
  (.branch 49 (.branch 30 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 49 (.branch 48 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 17 (.leaf (-2)) (.branch 36 (.leaf (-1)) (.leaf (0))))]
def witnessD6_001_26 : CycleWitness 6 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (3)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (2)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (2)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (1))))))))
  code := certificateD6_26
  counts := ![(.branch 24 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 37 (.branch 29 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 32 (.leaf (12)) (.branch 34 (.leaf (13)) (.leaf (14))))) (.branch 45 (.branch 40 (.leaf (15)) (.branch 42 (.leaf (16)) (.leaf (17)))) (.branch 47 (.leaf (18)) (.branch 50 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 13 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 39 (.branch 30 (.branch 28 (.leaf (10)) (.leaf (11))) (.branch 33 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14))))) (.branch 46 (.branch 41 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17)))) (.branch 49 (.leaf (18)) (.branch 52 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-2)) (.leaf (-4)))) (.branch 30 (.leaf (-5)) (.branch 43 (.leaf (-6)) (.leaf (-7))))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-30))),
  (.branch 48 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 48 (.leaf (-12)) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 47 (.branch 44 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-2)) (.leaf (0))))),
  (.branch 45 (.leaf (-3)) (.leaf (-2))),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 29 (.branch 25 (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))) (.branch 27 (.branch 26 (.leaf (-27)) (.leaf (-26))) (.branch 28 (.leaf (-25)) (.leaf (-24))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.leaf (-20)))) (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_001_27 : CycleWitness 6 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (5)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (5)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (4)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (5)) (.leaf (2))))))))
  code := certificateD6_27
  counts := ![(.branch 23 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 39 (.branch 29 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 43 (.branch 41 (.leaf (14)) (.leaf (15))) (.branch 47 (.leaf (16)) (.branch 49 (.leaf (17)) (.leaf (18))))))),
  (.branch 24 (.branch 11 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 17 (.leaf (-3)) (.branch 43 (.leaf (-4)) (.leaf (-5))))),
  (.branch 20 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 14 (.leaf (-6)) (.leaf (-7)))) (.branch 40 (.branch 30 (.leaf (-9)) (.leaf (-10))) (.branch 46 (.leaf (-11)) (.leaf (-13))))),
  (.branch 5 (.leaf (0)) (.branch 31 (.leaf (-5)) (.leaf (-7)))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3)))),
  (.branch 47 (.leaf (-13)) (.branch 51 (.leaf (-12)) (.leaf (-10)))),
  (.branch 39 (.branch 32 (.leaf (-7)) (.leaf (-6))) (.branch 46 (.leaf (-5)) (.branch 47 (.leaf (-2)) (.leaf (0))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 43 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 34 (.leaf (-5)) (.leaf (-3)))]
def witnessD6_001_28 : CycleWitness 6 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (5)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (2)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (4)) (.branch 44 (.leaf (0)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (5)) (.leaf (3))))))))
  code := certificateD6_28
  counts := ![(.branch 24 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 20 (.leaf (9)) (.branch 22 (.leaf (10)) (.leaf (11)))))) (.branch 37 (.branch 31 (.branch 27 (.leaf (12)) (.branch 29 (.leaf (13)) (.leaf (14)))) (.branch 33 (.leaf (15)) (.branch 35 (.leaf (16)) (.leaf (17))))) (.branch 44 (.branch 40 (.leaf (18)) (.branch 42 (.leaf (19)) (.leaf (20)))) (.branch 48 (.branch 46 (.leaf (21)) (.leaf (22))) (.branch 50 (.leaf (23)) (.leaf (24))))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-8)))) (.branch 9 (.branch 7 (.leaf (-9)) (.leaf (-10))) (.branch 11 (.leaf (-11)) (.leaf (-12))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-14)) (.leaf (-16)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-28)) (.leaf (-29)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (-1))) (.branch 51 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 51 (.leaf (-12)) (.leaf (-6))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.branch 39 (.leaf (-16)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 47 (.branch 44 (.branch 26 (.leaf (-29)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (-3))]
def witnessD6_001_29 : CycleWitness 6 where
  length := 52
  word := (.branch 26 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (2)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (4))))))) (.branch 38 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (1)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (3)) (.branch 34 (.leaf (5)) (.leaf (0)))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (2)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (2)))) (.branch 43 (.leaf (4)) (.branch 44 (.leaf (0)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (0)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (1)) (.leaf (5))))))))
  code := certificateD6_29
  counts := ![(.branch 24 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 38 (.branch 29 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 44 (.branch 41 (.leaf (14)) (.leaf (15))) (.branch 47 (.leaf (16)) (.branch 50 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 31 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.branch 51 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-17)) (.leaf (-25)))),
  (.branch 25 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 14 (.leaf (-3)) (.leaf (-6)))) (.branch 31 (.branch 28 (.leaf (-7)) (.leaf (-8))) (.branch 40 (.leaf (-9)) (.branch 51 (.leaf (-12)) (.leaf (-13)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 42 (.leaf (-12)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-28))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 39 (.branch 33 (.branch 30 (.leaf (-25)) (.leaf (-24))) (.branch 36 (.leaf (-23)) (.leaf (-22)))) (.branch 45 (.branch 42 (.leaf (-21)) (.leaf (-20))) (.branch 48 (.leaf (-19)) (.branch 51 (.leaf (-18)) (.leaf (-9)))))),
  (.leaf (-13)),
  (.branch 50 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 51 (.leaf (-10)) (.leaf (-7)))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.branch 44 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 35 (.leaf (-2)) (.leaf (0)))]
def witnessD6_001_30 : CycleWitness 6 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (2)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (5)) (.branch 31 (.leaf (2)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (1)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (1)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (5)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (2)) (.leaf (1))))))))
  code := certificateD6_30
  counts := ![(.branch 23 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 29 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 49 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 12 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.branch 52 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 31 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 29 (.leaf (-11)) (.leaf (-13)))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-5)))) (.branch 34 (.branch 28 (.leaf (-6)) (.leaf (-7))) (.branch 44 (.leaf (-9)) (.leaf (-10))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (-1)) (.leaf (-4)))) (.branch 35 (.leaf (-6)) (.branch 45 (.leaf (-7)) (.leaf (-9))))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-40)) (.leaf (-41)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (-13))) (.branch 47 (.leaf (-14)) (.leaf (-15))))]
  high := ![(.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-10)) (.leaf (-7)))),
  (.branch 49 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-5)) (.leaf (-3))))),
  (.branch 46 (.leaf (-9)) (.leaf (-8))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 45 (.branch 41 (.branch 22 (.leaf (-41)) (.branch 40 (.leaf (-39)) (.leaf (-36)))) (.branch 43 (.branch 42 (.leaf (-33)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))]
def witnessD6_001_31 : CycleWitness 6 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (3)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (2))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (0)) (.leaf (2))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (2)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (3)) (.leaf (1)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (0)))) (.branch 41 (.leaf (2)) (.branch 42 (.leaf (1)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (0)) (.leaf (5)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (3)) (.leaf (2))))))))
  code := certificateD6_31
  counts := ![(.branch 23 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))) (.branch 35 (.branch 28 (.branch 26 (.leaf (10)) (.leaf (11))) (.branch 30 (.leaf (12)) (.branch 33 (.leaf (13)) (.leaf (14))))) (.branch 43 (.branch 38 (.leaf (15)) (.branch 40 (.leaf (16)) (.leaf (17)))) (.branch 45 (.leaf (18)) (.branch 48 (.leaf (19)) (.leaf (20))))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 42 (.leaf (8)) (.branch 47 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 9 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 31 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (-3))) (.branch 34 (.leaf (-5)) (.branch 44 (.leaf (-8)) (.leaf (-10))))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (-3)) (.leaf (-5))))]
  high := ![(.branch 46 (.leaf (-5)) (.branch 49 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8)))) (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5))))),
  (.branch 37 (.leaf (-3)) (.leaf (-2))),
  (.branch 44 (.branch 41 (.branch 22 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))) (.branch 42 (.leaf (-10)) (.branch 43 (.leaf (-9)) (.leaf (-8))))) (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.leaf (-2))))]
def witnessD6_001_32 : CycleWitness 6 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (4)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (0)) (.leaf (5))))))
  code := certificateD6_32
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (4))))) (.branch 8 (.branch 7 (.leaf (5)) (.leaf (6))) (.branch 9 (.leaf (7)) (.branch 10 (.leaf (8)) (.leaf (9)))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (10)) (.leaf (11))) (.branch 15 (.leaf (12)) (.branch 16 (.leaf (13)) (.leaf (14))))) (.branch 20 (.branch 19 (.leaf (15)) (.leaf (16))) (.branch 21 (.leaf (17)) (.branch 22 (.leaf (18)) (.leaf (19))))))) (.branch 35 (.branch 29 (.branch 26 (.branch 25 (.leaf (20)) (.leaf (21))) (.branch 27 (.leaf (22)) (.branch 28 (.leaf (23)) (.leaf (24))))) (.branch 32 (.branch 31 (.leaf (25)) (.leaf (26))) (.branch 33 (.leaf (27)) (.branch 34 (.leaf (28)) (.leaf (29)))))) (.branch 41 (.branch 38 (.branch 37 (.leaf (30)) (.leaf (31))) (.branch 39 (.leaf (32)) (.branch 40 (.leaf (33)) (.leaf (34))))) (.branch 45 (.branch 43 (.leaf (35)) (.branch 44 (.leaf (36)) (.leaf (37)))) (.branch 46 (.leaf (38)) (.branch 47 (.leaf (39)) (.leaf (40)))))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))) (.branch 4 (.leaf (-3)) (.branch 5 (.leaf (-4)) (.leaf (-5))))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-36))),
  (.branch 24 (.leaf (0)) (.leaf (-24))),
  (.branch 36 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.leaf (-5)),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 21 (.branch 16 (.branch 14 (.branch 13 (.leaf (-36)) (.leaf (-35))) (.branch 15 (.leaf (-34)) (.leaf (-33)))) (.branch 18 (.branch 17 (.leaf (-32)) (.leaf (-31))) (.branch 19 (.leaf (-30)) (.branch 20 (.leaf (-29)) (.leaf (-28)))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-27)) (.leaf (-26))) (.branch 24 (.leaf (-25)) (.leaf (-24)))) (.branch 27 (.branch 26 (.leaf (-23)) (.leaf (-22))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))))) (.branch 39 (.branch 34 (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))) (.branch 33 (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_001_33 : CycleWitness 6 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.leaf (2)))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (4)))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (3))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_33
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.leaf (7))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (8)) (.leaf (9))) (.branch 16 (.leaf (10)) (.leaf (11)))) (.branch 20 (.branch 19 (.leaf (12)) (.leaf (13))) (.branch 22 (.leaf (14)) (.leaf (15)))))) (.branch 35 (.branch 29 (.branch 26 (.branch 25 (.leaf (16)) (.leaf (17))) (.branch 28 (.leaf (18)) (.leaf (19)))) (.branch 32 (.branch 31 (.leaf (20)) (.leaf (21))) (.branch 34 (.leaf (22)) (.leaf (23))))) (.branch 41 (.branch 38 (.branch 37 (.leaf (24)) (.leaf (25))) (.branch 40 (.leaf (26)) (.leaf (27)))) (.branch 44 (.branch 43 (.leaf (28)) (.leaf (29))) (.branch 46 (.leaf (30)) (.branch 47 (.leaf (31)) (.leaf (32)))))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.branch 24 (.leaf (0)) (.leaf (-24))),
  (.leaf (0))]
  high := ![(.leaf (-2)),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))) (.branch 33 (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD6_001_34 : CycleWitness 6 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (0)) (.leaf (1))))))) (.branch 36 (.branch 31 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (0))))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (1)))))) (.branch 43 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (0))))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (0))) (.branch 46 (.leaf (5)) (.branch 47 (.leaf (0)) (.leaf (1))))))))
  code := certificateD6_34
  counts := ![(.branch 23 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 16 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))) (.branch 19 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 21 (.leaf (12)) (.leaf (13)))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (14)) (.branch 26 (.leaf (15)) (.leaf (16)))) (.branch 31 (.branch 30 (.leaf (17)) (.leaf (18))) (.branch 33 (.leaf (19)) (.leaf (20))))) (.branch 42 (.branch 38 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 40 (.leaf (23)) (.leaf (24)))) (.branch 45 (.branch 43 (.leaf (25)) (.leaf (26))) (.branch 47 (.leaf (27)) (.leaf (28))))))),
  (.branch 24 (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 46 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-14))),
  (.branch 22 (.leaf (0)) (.leaf (-26))),
  (.branch 46 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 44 (.leaf (-11)) (.branch 46 (.leaf (-9)) (.leaf (-7)))),
  (.branch 40 (.leaf (-1)) (.leaf (0))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 41 (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.branch 28 (.branch 25 (.branch 23 (.leaf (-26)) (.branch 24 (.leaf (-25)) (.leaf (-24)))) (.branch 26 (.leaf (-23)) (.branch 27 (.leaf (-22)) (.leaf (-21))))) (.branch 31 (.branch 29 (.leaf (-20)) (.branch 30 (.leaf (-19)) (.leaf (-18)))) (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))))) (.branch 41 (.branch 38 (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))) (.branch 39 (.leaf (-10)) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_001 : Fin 19 → CycleWitness 6 := ![witnessD6_001_16, witnessD6_001_17, witnessD6_001_18, witnessD6_001_19, witnessD6_001_20, witnessD6_001_21, witnessD6_001_22, witnessD6_001_23, witnessD6_001_24, witnessD6_001_25, witnessD6_001_26, witnessD6_001_27, witnessD6_001_28, witnessD6_001_29, witnessD6_001_30, witnessD6_001_31, witnessD6_001_32, witnessD6_001_33, witnessD6_001_34]
end RealPinwheel.FiveSixths


