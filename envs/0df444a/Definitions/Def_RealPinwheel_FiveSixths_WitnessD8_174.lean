-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_174
-- name    : RealPinwheel_FiveSixths_WitnessD8_174
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:25:43.924045+00:00
-- url     : https://prove2.me/theorems/bde01d6a-d68b-4679-85ca-7fd8690a223c
-- title:
--   Exact witness block D8_174
-- statement:
--   These exact witnesses represent words 1705 through 1722 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1705–1722; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_174_1704 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (5)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (7)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (6)) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (5)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (3)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (0)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (4)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (7)) (.branch 49 (.leaf (3)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (5))))))))
  code := certificateD8_1704
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 28 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 18 (.leaf (-9)) (.branch 45 (.leaf (-14)) (.leaf (-18))))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (-9))) (.branch 44 (.leaf (-11)) (.leaf (-13)))),
  (.branch 17 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-20))),
  (.branch 21 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 43 (.leaf (-7)) (.leaf (-6))),
  (.branch 48 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 46 (.leaf (-18)) (.leaf (-17))) (.branch 53 (.leaf (-14)) (.leaf (-11)))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-13)) (.leaf (-12))) (.branch 47 (.leaf (-11)) (.branch 48 (.leaf (-10)) (.leaf (-9))))) (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 18 (.leaf (-2)) (.branch 38 (.leaf (-1)) (.leaf (0)))),
  (.branch 44 (.branch 39 (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16))))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_174_1705 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (7))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (6)) (.branch 35 (.leaf (0)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (3)) (.branch 42 (.leaf (0)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (4))) (.branch 46 (.leaf (0)) (.leaf (7))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (0)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (3)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (5))))))))
  code := certificateD8_1705
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 48 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 28 (.leaf (-17)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-13)) (.leaf (-17)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 43 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 31 (.leaf (-11)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-20))),
  (.branch 20 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 36 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-13))))),
  (.branch 45 (.branch 41 (.leaf (-17)) (.leaf (-16))) (.branch 49 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.branch 52 (.branch 51 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 42 (.branch 32 (.leaf (-14)) (.leaf (-13))) (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-10)) (.leaf (-8))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 44 (.branch 39 (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16))))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_174_1706 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (3)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (5)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (1)) (.leaf (6))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (4))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (2))) (.branch 39 (.leaf (3)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (5)) (.branch 42 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (4)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_1706
  counts := ![(.branch 24 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 51 (.leaf (13)) (.leaf (14)))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 42 (.branch 34 (.branch 29 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 50 (.branch 45 (.leaf (11)) (.leaf (12))) (.branch 53 (.leaf (13)) (.leaf (14)))))),
  (.branch 25 (.branch 11 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-20)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.branch 29 (.leaf (-2)) (.leaf (-3)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 38 (.leaf (-14)) (.leaf (-17)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.leaf (-13))),
  (.branch 27 (.leaf (0)) (.leaf (-27))),
  (.leaf (0))]
  high := ![(.branch 52 (.branch 48 (.leaf (-22)) (.leaf (-21))) (.branch 53 (.leaf (-14)) (.leaf (-7)))),
  (.leaf (-3)),
  (.branch 39 (.leaf (-17)) (.branch 53 (.leaf (-16)) (.leaf (-11)))),
  (.branch 51 (.branch 40 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-26)) (.leaf (-25)))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22))))) (.branch 36 (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19)))) (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 39 (.leaf (-16)) (.leaf (-15)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_174_1707 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (7)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (6))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (4)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (0)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (6)) (.leaf (2))) (.branch 46 (.leaf (0)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (3)) (.branch 49 (.leaf (5)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_1707
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 28 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 18 (.leaf (-9)) (.branch 45 (.leaf (-14)) (.leaf (-18))))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (-9))) (.branch 44 (.leaf (-11)) (.leaf (-13)))),
  (.branch 17 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 43 (.leaf (-7)) (.leaf (-6))),
  (.branch 48 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 46 (.leaf (-18)) (.leaf (-17))) (.branch 53 (.leaf (-14)) (.leaf (-11)))),
  (.branch 50 (.branch 35 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-13)) (.leaf (-12))) (.branch 47 (.leaf (-11)) (.branch 48 (.leaf (-10)) (.leaf (-9))))) (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 18 (.leaf (-2)) (.branch 38 (.leaf (-1)) (.leaf (0))))]
def witnessD8_174_1708 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (7)) (.leaf (0))) (.branch 19 (.leaf (2)) (.leaf (5))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (4)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (6))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (5))))) (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (3))) (.branch 39 (.leaf (0)) (.leaf (4)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (6)) (.leaf (0))) (.branch 46 (.leaf (3)) (.leaf (5))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (4)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (3)) (.leaf (7))))))))
  code := certificateD8_1708
  counts := ![(.branch 25 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.branch 52 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 41 (.leaf (-22)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.branch 29 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 26 (.leaf (-33)) (.leaf (-34)))),
  (.branch 30 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 53 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (-9))) (.branch 44 (.leaf (-11)) (.leaf (-13)))),
  (.branch 17 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 49 (.branch 42 (.leaf (-25)) (.leaf (-24))) (.branch 53 (.leaf (-20)) (.leaf (-13)))),
  (.branch 52 (.branch 44 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 43 (.branch 27 (.leaf (-34)) (.branch 35 (.leaf (-32)) (.leaf (-30)))) (.branch 52 (.branch 51 (.leaf (-28)) (.leaf (-21))) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.leaf (-7)),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 48 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-13)) (.leaf (-12))) (.branch 47 (.leaf (-11)) (.branch 48 (.leaf (-10)) (.leaf (-9))))) (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 18 (.leaf (-2)) (.branch 38 (.leaf (-1)) (.leaf (0))))]
def witnessD8_174_1709 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (5)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (7)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (3)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (6)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (3)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (7))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (6))))) (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (5)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (7)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (2)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (3))) (.branch 46 (.leaf (6)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (5)) (.branch 49 (.leaf (2)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (4)) (.leaf (0))) (.branch 53 (.leaf (3)) (.leaf (7))))))))
  code := certificateD8_1709
  counts := ![(.branch 25 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 20 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 47 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-33)) (.leaf (-36)))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 45 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.branch 31 (.leaf (-11)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.branch 12 (.leaf (0)) (.branch 39 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 48 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 44 (.branch 30 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-17)))) (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-12))) (.branch 53 (.leaf (-8)) (.leaf (-4))))),
  (.branch 51 (.branch 19 (.leaf (-36)) (.branch 50 (.leaf (-35)) (.leaf (-28)))) (.branch 52 (.leaf (-21)) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.branch 46 (.leaf (-9)) (.leaf (-7))),
  (.branch 42 (.branch 32 (.leaf (-14)) (.leaf (-13))) (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-10)) (.leaf (-8))))),
  (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 41 (.branch 40 (.leaf (-3)) (.leaf (-2))) (.branch 42 (.leaf (-1)) (.leaf (0))))]
def witnessD8_174_1710 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (6)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (7)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (6)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (2))) (.branch 26 (.leaf (3)) (.leaf (1))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (7)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (3)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (5))) (.branch 39 (.leaf (6)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (0)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (0)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (7)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (5)) (.leaf (2))) (.branch 53 (.leaf (3)) (.leaf (1))))))))
  code := certificateD8_1710
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 23 (.leaf (-7)) (.leaf (-8)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 29 (.leaf (-4)) (.branch 43 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (-14))) (.branch 39 (.leaf (-16)) (.leaf (-18)))),
  (.branch 12 (.leaf (0)) (.branch 49 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.branch 49 (.leaf (-7)) (.branch 50 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.leaf (-4)) (.branch 53 (.leaf (-3)) (.leaf (-2))))),
  (.branch 42 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (-1)),
  (.branch 49 (.branch 46 (.branch 32 (.leaf (-19)) (.leaf (-18))) (.branch 47 (.leaf (-16)) (.branch 48 (.leaf (-14)) (.leaf (-12))))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 46 (.branch 42 (.branch 40 (.leaf (-18)) (.branch 41 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 45 (.leaf (-13)) (.leaf (-12))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.leaf (-8)))) (.branch 52 (.branch 51 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))))]
def witnessD8_174_1711 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (6)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (7)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (6)) (.branch 42 (.leaf (0)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (4))) (.branch 46 (.leaf (0)) (.leaf (3))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (0)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (7)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (5))))))))
  code := certificateD8_1711
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 48 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 28 (.leaf (-17)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-13)) (.leaf (-17)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 43 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (-13)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 41 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (-5)) (.leaf (-7))))]
  high := ![(.branch 36 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-13))))),
  (.branch 45 (.branch 41 (.leaf (-17)) (.leaf (-16))) (.branch 49 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.branch 52 (.branch 51 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 50 (.branch 48 (.leaf (-14)) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-16)) (.branch 43 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11))))) (.branch 50 (.branch 48 (.leaf (-10)) (.branch 49 (.leaf (-9)) (.leaf (-8)))) (.branch 52 (.branch 51 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 52 (.branch 32 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4))))]
def witnessD8_174_1712 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (4)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (7))) (.branch 19 (.leaf (1)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (0)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (3)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (5)) (.leaf (0))) (.branch 39 (.leaf (4)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (0)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (7)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (4)) (.branch 49 (.leaf (1)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (5)) (.leaf (2))) (.branch 53 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_1712
  counts := ![(.branch 26 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 30 (.leaf (7)) (.branch 34 (.leaf (8)) (.leaf (9)))) (.branch 47 (.branch 42 (.leaf (10)) (.leaf (11))) (.branch 50 (.leaf (12)) (.leaf (13)))))),
  (.branch 28 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 33 (.leaf (7)) (.branch 36 (.leaf (8)) (.leaf (9)))) (.branch 49 (.branch 45 (.leaf (10)) (.leaf (11))) (.branch 53 (.leaf (12)) (.leaf (13)))))),
  (.branch 25 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 48 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-19)) (.leaf (-20)))) (.branch 17 (.branch 13 (.leaf (-21)) (.leaf (-22))) (.branch 50 (.leaf (-23)) (.leaf (-25))))),
  (.branch 23 (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-5)) (.leaf (-7)))) (.branch 40 (.branch 36 (.leaf (-8)) (.leaf (-9))) (.branch 53 (.leaf (-10)) (.leaf (-11))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 29 (.leaf (-6)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (-11))) (.branch 48 (.leaf (-16)) (.leaf (-19)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (-5))) (.branch 37 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-23))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 52 (.branch 51 (.leaf (-25)) (.leaf (-19))) (.branch 53 (.leaf (-13)) (.leaf (-7)))),
  (.leaf (-11)),
  (.branch 47 (.branch 30 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-4)))),
  (.branch 22 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.branch 44 (.leaf (-1)) (.leaf (0))))),
  (.branch 51 (.branch 49 (.leaf (-19)) (.branch 50 (.leaf (-17)) (.leaf (-15)))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-11)) (.leaf (-9))))),
  (.branch 52 (.branch 38 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 42 (.branch 36 (.branch 33 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19))))) (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_174_1713 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (7)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (5)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (6)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (1)) (.leaf (5))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (7)) (.branch 32 (.leaf (0)) (.leaf (4))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (3)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (2))) (.branch 39 (.leaf (6)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (5)) (.branch 42 (.leaf (1)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (4)) (.leaf (0))))) (.branch 50 (.branch 48 (.leaf (2)) (.branch 49 (.leaf (7)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (3))) (.branch 53 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_1713
  counts := ![(.branch 24 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 51 (.leaf (13)) (.leaf (14)))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 42 (.branch 34 (.branch 29 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 50 (.branch 45 (.leaf (11)) (.leaf (12))) (.branch 53 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-20)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.branch 29 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 39 (.leaf (-14)) (.leaf (-15)))),
  (.branch 12 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 52 (.branch 48 (.leaf (-22)) (.leaf (-21))) (.branch 53 (.leaf (-14)) (.leaf (-7)))),
  (.leaf (-3)),
  (.branch 50 (.branch 39 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 46 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9))))) (.branch 50 (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 13 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_174_1714 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (5)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (7)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (0))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (5)) (.leaf (0)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (2)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (7)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (5)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (0))) (.branch 46 (.leaf (1)) (.leaf (3))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (6)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (4)) (.leaf (5))))))))
  code := certificateD8_1714
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.leaf (15)))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 28 (.leaf (-12)) (.branch 46 (.leaf (-14)) (.leaf (-16))))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-4)))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (-10))) (.branch 47 (.leaf (-14)) (.leaf (-17)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (-5))) (.branch 36 (.leaf (-8)) (.leaf (-12)))),
  (.branch 29 (.leaf (0)) (.branch 42 (.leaf (-3)) (.leaf (-6)))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 49 (.branch 38 (.leaf (-13)) (.leaf (-12))) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.branch 52 (.branch 47 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-12)) (.leaf (-9)))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 50 (.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 52 (.branch 51 (.leaf (-14)) (.leaf (-13))) (.branch 53 (.leaf (-12)) (.leaf (-11))))),
  (.branch 37 (.leaf (-12)) (.leaf (-11))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 47 (.branch 46 (.leaf (-3)) (.leaf (-2))) (.branch 48 (.leaf (-1)) (.leaf (0))))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.branch 43 (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_174_1715 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (5)) (.leaf (7))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (4)) (.leaf (6))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (5)) (.branch 35 (.leaf (0)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (0))) (.branch 39 (.leaf (4)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (0)) (.leaf (3)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (0))) (.branch 46 (.leaf (5)) (.leaf (6))))) (.branch 50 (.branch 48 (.leaf (1)) (.branch 49 (.leaf (0)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (4)) (.leaf (7))))))))
  code := certificateD8_1715
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 31 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.branch 51 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 48 (.branch 44 (.leaf (11)) (.leaf (12))) (.branch 52 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 24 (.leaf (-20)) (.branch 51 (.leaf (-24)) (.leaf (-27))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-13)) (.leaf (-18)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-21)) (.leaf (-22)))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (-7))) (.branch 46 (.leaf (-9)) (.leaf (-10)))),
  (.branch 10 (.leaf (0)) (.branch 27 (.leaf (-9)) (.leaf (-11)))),
  (.branch 37 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 52 (.leaf (-27)) (.branch 53 (.leaf (-20)) (.leaf (-13)))),
  (.branch 45 (.branch 37 (.leaf (-18)) (.branch 41 (.leaf (-17)) (.leaf (-16)))) (.branch 49 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-7))))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-22)) (.leaf (-20))) (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-16)) (.leaf (-14))))) (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-10)) (.leaf (-8)))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 40 (.leaf (-3)) (.leaf (-2))),
  (.branch 50 (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.leaf (-7)))) (.branch 52 (.branch 51 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-3))))),
  (.branch 50 (.branch 48 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.leaf (-8)))) (.branch 52 (.branch 51 (.leaf (-7)) (.leaf (-6))) (.branch 53 (.leaf (-5)) (.leaf (-4))))),
  (.branch 38 (.leaf (-1)) (.leaf (0)))]
def witnessD8_174_1716 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (3)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (4))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (0)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (6)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (4))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (5)) (.leaf (7))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (4))) (.branch 39 (.leaf (3)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (6)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (5))) (.branch 46 (.leaf (0)) (.leaf (4))))) (.branch 50 (.branch 48 (.leaf (3)) (.branch 49 (.leaf (0)) (.leaf (1)))) (.branch 52 (.branch 51 (.leaf (7)) (.leaf (0))) (.branch 53 (.leaf (2)) (.leaf (4))))))))
  code := certificateD8_1716
  counts := ![(.branch 25 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))) (.branch 40 (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.branch 37 (.leaf (12)) (.leaf (13))))) (.branch 46 (.branch 43 (.leaf (14)) (.leaf (15))) (.branch 49 (.leaf (16)) (.branch 52 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 11 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 42 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 27 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.branch 6 (.leaf (0)) (.branch 41 (.leaf (-12)) (.leaf (-13)))),
  (.branch 14 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 51 (.branch 43 (.leaf (-7)) (.leaf (-6))) (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-1)),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 48 (.leaf (-3)) (.leaf (-2))) (.branch 50 (.leaf (-1)) (.leaf (0)))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-18)) (.leaf (-16))) (.branch 48 (.leaf (-14)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-10)) (.leaf (-8))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 47 (.branch 44 (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 50 (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_174_1717 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (7)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (6))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (4)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (5)) (.branch 35 (.leaf (0)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (2)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (0)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (6)) (.leaf (3))) (.branch 46 (.leaf (0)) (.leaf (1))))) (.branch 50 (.branch 48 (.leaf (5)) (.branch 49 (.leaf (2)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (4)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_1717
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 45 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 28 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 24 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 45 (.leaf (-9)) (.leaf (-10)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-2)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (-9))) (.branch 44 (.leaf (-11)) (.leaf (-13)))),
  (.branch 17 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 43 (.leaf (-7)) (.leaf (-6))),
  (.branch 48 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-9))) (.branch 48 (.leaf (-8)) (.leaf (-7)))) (.branch 51 (.branch 50 (.leaf (-6)) (.leaf (-5))) (.branch 52 (.leaf (-4)) (.branch 53 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 52 (.leaf (-4)) (.branch 53 (.leaf (-3)) (.leaf (-2)))),
  (.branch 50 (.branch 35 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-10)))) (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 46 (.branch 45 (.leaf (-13)) (.leaf (-12))) (.branch 47 (.leaf (-11)) (.branch 48 (.leaf (-10)) (.leaf (-9))))) (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 18 (.leaf (-2)) (.branch 38 (.leaf (-1)) (.leaf (0))))]
def witnessD8_174_1718 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (2)) (.leaf (7)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (5))) (.branch 19 (.leaf (1)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (0)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (6))) (.branch 26 (.leaf (2)) (.leaf (5))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (4)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (7)) (.branch 35 (.leaf (1)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (0))) (.branch 39 (.leaf (3)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (2)) (.leaf (6)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (5))) (.branch 46 (.leaf (1)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (3)) (.branch 49 (.leaf (0)) (.leaf (4)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (7))) (.branch 53 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_1718
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-22))) (.branch 11 (.leaf (-24)) (.leaf (-26)))),
  (.branch 2 (.leaf (0)) (.leaf (-17))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 51 (.branch 39 (.leaf (-26)) (.branch 50 (.leaf (-25)) (.leaf (-20)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 41 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 48 (.leaf (-8)) (.leaf (-5))),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_174_1719 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (5)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (3)) (.leaf (1))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (6)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (3)) (.leaf (4)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (1)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (3))) (.branch 46 (.leaf (1)) (.leaf (2))))) (.branch 50 (.branch 48 (.leaf (0)) (.branch 49 (.leaf (4)) (.leaf (3)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_1719
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.leaf (15)))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 45 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1))),
  (.branch 53 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 28 (.leaf (-12)) (.branch 46 (.leaf (-14)) (.leaf (-16))))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 17 (.leaf (0)) (.leaf (-37))),
  (.branch 35 (.leaf (0)) (.leaf (-19))),
  (.branch 53 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 49 (.branch 45 (.leaf (-14)) (.leaf (-12))) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.branch 52 (.branch 47 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-12)) (.leaf (-9)))),
  (.branch 48 (.leaf (-1)) (.leaf (0))),
  (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))),
  (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (-37)) (.leaf (-36))) (.branch 20 (.leaf (-35)) (.leaf (-34)))) (.branch 23 (.branch 22 (.leaf (-33)) (.leaf (-32))) (.branch 24 (.leaf (-31)) (.branch 25 (.leaf (-30)) (.leaf (-29)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-28)) (.leaf (-27))) (.branch 29 (.leaf (-26)) (.leaf (-25)))) (.branch 32 (.branch 31 (.leaf (-24)) (.leaf (-23))) (.branch 33 (.leaf (-22)) (.branch 34 (.leaf (-21)) (.leaf (-20))))))) (.branch 44 (.branch 39 (.branch 37 (.branch 36 (.leaf (-19)) (.leaf (-18))) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 44 (.branch 39 (.branch 37 (.branch 36 (.leaf (-19)) (.leaf (-18))) (.branch 38 (.leaf (-17)) (.leaf (-16)))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-11)))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6))))) (.branch 51 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD8_174_1720 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (7)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (5))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (6))) (.branch 26 (.leaf (4)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 34 (.leaf (7)) (.branch 35 (.leaf (1)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (3)) (.leaf (1)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (5)) (.leaf (6)))) (.branch 45 (.branch 44 (.leaf (2)) (.leaf (1))) (.branch 46 (.leaf (0)) (.leaf (4))))) (.branch 50 (.branch 48 (.leaf (3)) (.branch 49 (.leaf (2)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (1)) (.leaf (7))) (.branch 53 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_1720
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 33 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.branch 36 (.leaf (-34)) (.leaf (-36)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-6))) (.branch 53 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 46 (.leaf (-18)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 48 (.branch 37 (.leaf (-36)) (.leaf (-35))) (.branch 49 (.leaf (-30)) (.leaf (-25)))) (.branch 52 (.branch 51 (.leaf (-20)) (.leaf (-15))) (.branch 53 (.leaf (-10)) (.leaf (-5))))),
  (.branch 21 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5))))),
  (.branch 48 (.branch 45 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))) (.branch 51 (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))) (.branch 52 (.leaf (-3)) (.branch 53 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_174_1721 : CycleWitness 8 where
  length := 54
  word := (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (7)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (4)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (5))) (.branch 19 (.leaf (1)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (6))) (.branch 26 (.leaf (0)) (.leaf (2))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (7)) (.leaf (5)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (3))))) (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (6))) (.branch 39 (.leaf (4)) (.leaf (0)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (3)) (.branch 42 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 44 (.leaf (5)) (.leaf (0))) (.branch 46 (.leaf (1)) (.leaf (7))))) (.branch 50 (.branch 48 (.leaf (4)) (.branch 49 (.leaf (3)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (1))) (.branch 53 (.leaf (6)) (.leaf (4))))))))
  code := certificateD8_1721
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 45 (.leaf (9)) (.branch 50 (.leaf (10)) (.leaf (11)))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 34 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 46 (.leaf (9)) (.branch 52 (.leaf (10)) (.leaf (11)))))),
  (.branch 27 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 40 (.leaf (-43)) (.leaf (-46)))),
  (.branch 22 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))) (.branch 42 (.branch 37 (.leaf (-11)) (.leaf (-14))) (.branch 46 (.leaf (-15)) (.leaf (-18))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-11))) (.branch 27 (.leaf (-14)) (.leaf (-16)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 24 (.leaf (-7)) (.leaf (-8)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 30 (.leaf (-29)) (.leaf (-33)))),
  (.branch 25 (.branch 14 (.leaf (0)) (.leaf (-1))) (.branch 38 (.leaf (-8)) (.leaf (-11)))),
  (.branch 10 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 51 (.branch 41 (.leaf (-46)) (.branch 46 (.leaf (-45)) (.leaf (-44)))) (.branch 52 (.leaf (-33)) (.branch 53 (.leaf (-22)) (.leaf (-11))))),
  (.branch 47 (.leaf (-18)) (.branch 53 (.leaf (-17)) (.leaf (-15)))),
  (.branch 44 (.branch 28 (.leaf (-16)) (.branch 36 (.leaf (-15)) (.leaf (-14)))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-9)) (.leaf (-5))))),
  (.branch 51 (.branch 25 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3))))),
  (.branch 40 (.leaf (-1)) (.leaf (0))),
  (.branch 48 (.branch 45 (.branch 31 (.leaf (-33)) (.leaf (-32))) (.branch 46 (.leaf (-29)) (.branch 47 (.leaf (-26)) (.leaf (-23))))) (.branch 51 (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-17)) (.leaf (-14)))) (.branch 52 (.leaf (-11)) (.branch 53 (.leaf (-8)) (.leaf (-5)))))),
  (.branch 39 (.leaf (-11)) (.leaf (-10))),
  (.branch 50 (.branch 48 (.branch 11 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))) (.branch 52 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 53 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_174 : Fin 18 → CycleWitness 8 := ![witnessD8_174_1704, witnessD8_174_1705, witnessD8_174_1706, witnessD8_174_1707, witnessD8_174_1708, witnessD8_174_1709, witnessD8_174_1710, witnessD8_174_1711, witnessD8_174_1712, witnessD8_174_1713, witnessD8_174_1714, witnessD8_174_1715, witnessD8_174_1716, witnessD8_174_1717, witnessD8_174_1718, witnessD8_174_1719, witnessD8_174_1720, witnessD8_174_1721]
end RealPinwheel.FiveSixths


