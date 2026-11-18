-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_057
-- name    : RealPinwheel_FiveSixths_WitnessD7_057
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:03:38.85725+00:00
-- url     : https://prove2.me/theorems/e987645b-4fc0-4d87-9f04-08089961a602
-- title:
--   Exact witness block D7_057
-- statement:
--   These exact witnesses represent words 1002 through 1032 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 1002–1032; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_057_1001 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (3)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (4)) (.leaf (6)))))))
  code := certificateD7_1001
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 21 (.leaf (9)) (.leaf (10)))) (.branch 28 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.leaf (14)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 18 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-20))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-2)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 26 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-5)))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 16 (.branch 5 (.leaf (-20)) (.leaf (-19))) (.branch 27 (.leaf (-18)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3))))),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_057_1002 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.leaf (5)) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 25 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 26 (.leaf (6)) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1002
  counts := ![(.branch 15 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))))) (.branch 24 (.branch 18 (.branch 17 (.leaf (9)) (.leaf (10))) (.branch 20 (.leaf (11)) (.branch 22 (.leaf (12)) (.leaf (13))))) (.branch 27 (.branch 25 (.leaf (14)) (.leaf (15))) (.branch 29 (.leaf (16)) (.branch 31 (.leaf (17)) (.leaf (18))))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-22))),
  (.branch 26 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 28 (.branch 26 (.leaf (-15)) (.leaf (-13))) (.branch 30 (.leaf (-11)) (.leaf (-9)))),
  (.branch 22 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 21 (.branch 15 (.branch 12 (.branch 11 (.leaf (-22)) (.leaf (-21))) (.branch 13 (.leaf (-20)) (.branch 14 (.leaf (-19)) (.leaf (-18))))) (.branch 18 (.branch 16 (.leaf (-17)) (.branch 17 (.leaf (-16)) (.leaf (-15)))) (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_057_1003 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (5)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (3))) (.branch 31 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1003
  counts := ![(.branch 15 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 22 (.branch 18 (.branch 17 (.leaf (8)) (.leaf (9))) (.branch 20 (.leaf (10)) (.leaf (11)))) (.branch 26 (.branch 24 (.leaf (12)) (.leaf (13))) (.branch 28 (.leaf (14)) (.branch 31 (.leaf (15)) (.leaf (16))))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (-5)) (.leaf (-7)))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.branch 15 (.branch 4 (.leaf (-23)) (.leaf (-22))) (.branch 26 (.leaf (-21)) (.leaf (-18)))) (.branch 29 (.branch 28 (.leaf (-15)) (.leaf (-12))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 20 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_057_1004 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (6)) (.leaf (2))) (.branch 31 (.leaf (0)) (.leaf (1)))))))
  code := certificateD7_1004
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 21 (.leaf (9)) (.leaf (10)))) (.branch 28 (.branch 26 (.leaf (11)) (.leaf (12))) (.branch 31 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 18 (.leaf (-14)) (.leaf (-18)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-26))),
  (.branch 22 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.leaf (-19))),
  (.branch 29 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 24 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 29 (.leaf (-16)) (.leaf (-13)))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.branch 20 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 19 (.branch 12 (.branch 9 (.branch 7 (.leaf (-26)) (.branch 8 (.leaf (-25)) (.leaf (-24)))) (.branch 10 (.leaf (-23)) (.branch 11 (.leaf (-22)) (.leaf (-21))))) (.branch 15 (.branch 13 (.leaf (-20)) (.branch 14 (.leaf (-19)) (.leaf (-18)))) (.branch 17 (.branch 16 (.leaf (-17)) (.leaf (-16))) (.branch 18 (.leaf (-15)) (.leaf (-14)))))) (.branch 25 (.branch 22 (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))) (.branch 23 (.leaf (-10)) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-19)) (.leaf (-18))) (.branch 16 (.leaf (-17)) (.leaf (-16)))) (.branch 19 (.branch 18 (.leaf (-15)) (.leaf (-14))) (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_057_1005 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1005
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 21 (.leaf (9)) (.leaf (10)))) (.branch 28 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 18 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 16 (.leaf (0)) (.leaf (-16))),
  (.leaf (0))]
  high := ![(.branch 26 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-5)))),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-13)))) (.branch 22 (.branch 21 (.leaf (-12)) (.leaf (-11))) (.branch 23 (.leaf (-10)) (.leaf (-9))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_057_1006 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (4))) (.branch 31 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1006
  counts := ![(.branch 15 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 22 (.branch 18 (.branch 17 (.leaf (8)) (.leaf (9))) (.branch 20 (.leaf (10)) (.leaf (11)))) (.branch 26 (.branch 24 (.leaf (12)) (.leaf (13))) (.branch 28 (.leaf (14)) (.branch 31 (.leaf (15)) (.leaf (16))))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (-5)) (.leaf (-7)))),
  (.branch 11 (.leaf (0)) (.leaf (-21))),
  (.branch 27 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 15 (.branch 4 (.leaf (-23)) (.leaf (-22))) (.branch 26 (.leaf (-21)) (.leaf (-18)))) (.branch 29 (.branch 28 (.leaf (-15)) (.leaf (-12))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 20 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-21)) (.leaf (-20))) (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17))))) (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_057_1007 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (6)) (.leaf (0))) (.branch 31 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1007
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 27 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 18 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 28 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.leaf (12)))))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-2)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-19))),
  (.branch 29 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 28 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.leaf (-4)) (.leaf (-3))),
  (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-19)) (.leaf (-18))) (.branch 16 (.leaf (-17)) (.leaf (-16)))) (.branch 19 (.branch 18 (.leaf (-15)) (.leaf (-14))) (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_057_1008 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1008
  counts := ![(.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (8)) (.leaf (9))) (.branch 21 (.leaf (10)) (.leaf (11)))) (.branch 27 (.branch 25 (.leaf (12)) (.leaf (13))) (.branch 29 (.leaf (14)) (.branch 31 (.leaf (15)) (.leaf (16))))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-24))),
  (.branch 16 (.leaf (0)) (.leaf (-16))),
  (.branch 24 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.branch 14 (.branch 11 (.branch 9 (.leaf (-24)) (.branch 10 (.leaf (-23)) (.leaf (-22)))) (.branch 12 (.leaf (-21)) (.branch 13 (.leaf (-20)) (.leaf (-19))))) (.branch 17 (.branch 15 (.leaf (-18)) (.branch 16 (.leaf (-17)) (.leaf (-16)))) (.branch 18 (.leaf (-15)) (.branch 19 (.leaf (-14)) (.leaf (-13)))))) (.branch 26 (.branch 23 (.branch 21 (.leaf (-12)) (.branch 22 (.leaf (-11)) (.leaf (-10)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-13)))) (.branch 22 (.branch 21 (.leaf (-12)) (.leaf (-11))) (.branch 23 (.leaf (-10)) (.leaf (-9))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_057_1009 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (6)) (.leaf (4)))))))
  code := certificateD7_1009
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 21 (.leaf (9)) (.leaf (10)))) (.branch 28 (.branch 26 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.leaf (14)))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-11)) (.branch 7 (.leaf (-13)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 15 (.leaf (0)) (.leaf (-17))),
  (.branch 31 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 24 (.leaf (-15)) (.branch 31 (.leaf (-14)) (.leaf (-7)))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (-17)) (.leaf (-16))) (.branch 18 (.leaf (-15)) (.leaf (-14)))) (.branch 21 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 22 (.leaf (-11)) (.leaf (-10))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_057_1010 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1010
  counts := ![(.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (8)) (.leaf (9))) (.branch 21 (.leaf (10)) (.leaf (11)))) (.branch 27 (.branch 25 (.leaf (12)) (.leaf (13))) (.branch 29 (.leaf (14)) (.branch 31 (.leaf (15)) (.leaf (16))))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-20))),
  (.branch 28 (.leaf (0)) (.leaf (-4)))]
  high := ![(.leaf (-1)),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 23 (.branch 21 (.leaf (-12)) (.branch 22 (.leaf (-11)) (.leaf (-10)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 17 (.branch 14 (.branch 13 (.leaf (-20)) (.leaf (-19))) (.branch 15 (.leaf (-18)) (.branch 16 (.leaf (-17)) (.leaf (-16))))) (.branch 19 (.branch 18 (.leaf (-15)) (.leaf (-14))) (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_057_1011 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (5)))))) (.branch 24 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1011
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 21 (.leaf (9)) (.leaf (10)))) (.branch 28 (.branch 26 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 18 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-11)) (.branch 14 (.leaf (-13)) (.leaf (-14))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 23 (.leaf (-7)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-23))),
  (.branch 25 (.leaf (0)) (.leaf (-7))),
  (.branch 16 (.leaf (0)) (.leaf (-16))),
  (.leaf (0))]
  high := ![(.branch 31 (.leaf (-14)) (.leaf (-7))),
  (.branch 24 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8)))),
  (.branch 30 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.branch 14 (.branch 11 (.branch 10 (.leaf (-23)) (.leaf (-22))) (.branch 12 (.leaf (-21)) (.branch 13 (.leaf (-20)) (.leaf (-19))))) (.branch 17 (.branch 15 (.leaf (-18)) (.branch 16 (.leaf (-17)) (.leaf (-16)))) (.branch 18 (.leaf (-15)) (.branch 19 (.leaf (-14)) (.leaf (-13)))))) (.branch 26 (.branch 23 (.branch 21 (.leaf (-12)) (.branch 22 (.leaf (-11)) (.leaf (-10)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-13)))) (.branch 22 (.branch 21 (.leaf (-12)) (.leaf (-11))) (.branch 23 (.leaf (-10)) (.leaf (-9))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_057_1012 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (6))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1012
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 21 (.leaf (9)) (.leaf (10)))) (.branch 28 (.branch 26 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.leaf (14)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-11)) (.branch 14 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-26))),
  (.branch 22 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 31 (.leaf (-14)) (.leaf (-7))),
  (.branch 30 (.branch 24 (.leaf (-11)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 26 (.leaf (-5)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 12 (.branch 9 (.branch 7 (.leaf (-26)) (.branch 8 (.leaf (-25)) (.leaf (-24)))) (.branch 10 (.leaf (-23)) (.branch 11 (.leaf (-22)) (.leaf (-21))))) (.branch 15 (.branch 13 (.leaf (-20)) (.branch 14 (.leaf (-19)) (.leaf (-18)))) (.branch 17 (.branch 16 (.leaf (-17)) (.leaf (-16))) (.branch 18 (.leaf (-15)) (.leaf (-14)))))) (.branch 25 (.branch 22 (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))) (.branch 23 (.leaf (-10)) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_057_1013 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (5)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (3)) (.leaf (6)))))))
  code := certificateD7_1013
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 27 (.branch 24 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (-20)) (.leaf (-21)))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 28 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 26 (.leaf (-21)) (.branch 27 (.leaf (-18)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3))))),
  (.branch 10 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (-3)))),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_057_1014 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (6)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1014
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 27 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-6))) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-25))),
  (.branch 23 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 28 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 25 (.leaf (-8)) (.leaf (-5))),
  (.branch 30 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 19 (.branch 13 (.branch 10 (.branch 8 (.leaf (-25)) (.branch 9 (.leaf (-24)) (.leaf (-23)))) (.branch 11 (.leaf (-22)) (.branch 12 (.leaf (-21)) (.leaf (-20))))) (.branch 16 (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17)))) (.branch 17 (.leaf (-16)) (.branch 18 (.leaf (-15)) (.leaf (-14)))))) (.branch 25 (.branch 22 (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))) (.branch 23 (.leaf (-10)) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_057_1015 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (6)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (5)) (.leaf (4)))))))
  code := certificateD7_1015
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 27 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-2)) (.leaf (-4)))) (.branch 24 (.leaf (-5)) (.branch 29 (.leaf (-6)) (.leaf (-7))))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-17)) (.leaf (-18)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 31 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 28 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))),
  (.branch 29 (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-15)) (.leaf (-12)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-6)) (.leaf (-3))))),
  (.branch 11 (.leaf (-2)) (.branch 22 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (-17)) (.leaf (-16))) (.branch 18 (.leaf (-15)) (.leaf (-14)))) (.branch 21 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 22 (.leaf (-11)) (.leaf (-10))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_057_1016 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (6))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1016
  counts := ![(.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 17 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 19 (.leaf (-14)) (.leaf (-15)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 15 (.leaf (-10)) (.leaf (-11)))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-24))),
  (.branch 24 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 30 (.branch 20 (.leaf (-15)) (.leaf (-14))) (.branch 31 (.leaf (-10)) (.leaf (-6)))),
  (.branch 21 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-5))))),
  (.leaf (-5)),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 20 (.branch 14 (.branch 11 (.branch 9 (.leaf (-24)) (.branch 10 (.leaf (-23)) (.leaf (-22)))) (.branch 12 (.leaf (-21)) (.branch 13 (.leaf (-20)) (.leaf (-19))))) (.branch 17 (.branch 15 (.leaf (-18)) (.branch 16 (.leaf (-17)) (.leaf (-16)))) (.branch 18 (.leaf (-15)) (.branch 19 (.leaf (-14)) (.leaf (-13)))))) (.branch 26 (.branch 23 (.branch 21 (.leaf (-12)) (.branch 22 (.leaf (-11)) (.leaf (-10)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_057_1017 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (6)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (0))) (.branch 23 (.leaf (6)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (3)) (.leaf (5)))))))
  code := certificateD7_1017
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 27 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 4 (.leaf (0)) (.leaf (-20))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-2)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 28 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 28 (.branch 16 (.branch 5 (.leaf (-20)) (.leaf (-19))) (.branch 27 (.leaf (-18)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3))))),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 29 (.branch 17 (.leaf (-6)) (.leaf (-5))) (.branch 30 (.leaf (-4)) (.branch 31 (.leaf (-3)) (.leaf (-2))))),
  (.branch 22 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_057_1018 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (0))) (.branch 23 (.leaf (5)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (0)) (.leaf (5)))))))
  code := certificateD7_1018
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 29 (.branch 26 (.leaf (11)) (.leaf (12))) (.branch 31 (.leaf (13)) (.leaf (14)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-20)) (.leaf (-22)))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 20 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-7)))),
  (.branch 29 (.branch 19 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 26 (.branch 15 (.leaf (-22)) (.leaf (-21))) (.branch 27 (.leaf (-18)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3))))),
  (.branch 31 (.leaf (-6)) (.leaf (-3))),
  (.branch 29 (.branch 17 (.leaf (-6)) (.leaf (-5))) (.branch 30 (.leaf (-4)) (.branch 31 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_057_1019 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (4)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1019
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 27 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-22)) (.leaf (-24)))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 28 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.branch 9 (.leaf (-24)) (.branch 22 (.leaf (-23)) (.leaf (-20)))) (.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-10)) (.leaf (-5))))),
  (.branch 25 (.leaf (-8)) (.leaf (-5))),
  (.branch 30 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_057_1020 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (0))) (.branch 23 (.leaf (6)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1020
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 27 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-25))),
  (.branch 23 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 28 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 27 (.leaf (-2)) (.leaf (0))),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 19 (.branch 13 (.branch 10 (.branch 8 (.leaf (-25)) (.branch 9 (.leaf (-24)) (.leaf (-23)))) (.branch 11 (.leaf (-22)) (.branch 12 (.leaf (-21)) (.leaf (-20))))) (.branch 16 (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17)))) (.branch 17 (.leaf (-16)) (.branch 18 (.leaf (-15)) (.leaf (-14)))))) (.branch 25 (.branch 22 (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))) (.branch 23 (.leaf (-10)) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_057_1021 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (6)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1021
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 27 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-22)) (.leaf (-24)))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 16 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-25))),
  (.branch 23 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 28 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.branch 9 (.leaf (-24)) (.branch 22 (.leaf (-23)) (.leaf (-20)))) (.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-10)) (.leaf (-5))))),
  (.branch 25 (.leaf (-8)) (.leaf (-5))),
  (.branch 30 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.leaf (-2)) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 19 (.branch 13 (.branch 10 (.branch 8 (.leaf (-25)) (.branch 9 (.leaf (-24)) (.leaf (-23)))) (.branch 11 (.leaf (-22)) (.branch 12 (.leaf (-21)) (.leaf (-20))))) (.branch 16 (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17)))) (.branch 17 (.leaf (-16)) (.branch 18 (.leaf (-15)) (.leaf (-14)))))) (.branch 25 (.branch 22 (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))) (.branch 23 (.leaf (-10)) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_057_1022 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (6)) (.leaf (0))) (.branch 19 (.leaf (2)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (5)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (1)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1022
  counts := ![(.branch 14 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 16 (.leaf (-3)) (.branch 22 (.leaf (-4)) (.leaf (-6))))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-20))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0))]
  high := ![(.branch 26 (.branch 22 (.leaf (-14)) (.leaf (-13))) (.branch 30 (.leaf (-12)) (.branch 31 (.leaf (-9)) (.leaf (-6))))),
  (.branch 31 (.leaf (-6)) (.leaf (-5))),
  (.branch 25 (.leaf (-4)) (.leaf (-3))),
  (.branch 28 (.branch 16 (.branch 5 (.leaf (-20)) (.leaf (-19))) (.branch 27 (.leaf (-18)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3))))),
  (.branch 29 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_057_1023 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (5))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (5))) (.branch 31 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1023
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 29 (.branch 26 (.leaf (11)) (.leaf (12))) (.branch 31 (.leaf (13)) (.leaf (14)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-11)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 20 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-7)))),
  (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 28 (.branch 6 (.leaf (-17)) (.branch 17 (.leaf (-16)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.branch 23 (.branch 21 (.leaf (-12)) (.branch 22 (.leaf (-11)) (.leaf (-10)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_057_1024 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (3)) (.leaf (0))) (.branch 19 (.leaf (2)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (1)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1024
  counts := ![(.branch 14 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 16 (.leaf (-3)) (.branch 22 (.leaf (-4)) (.leaf (-6))))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (-1)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-20))),
  (.branch 11 (.leaf (0)) (.leaf (-21))),
  (.branch 28 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 26 (.branch 22 (.leaf (-14)) (.leaf (-13))) (.branch 30 (.leaf (-12)) (.branch 31 (.leaf (-9)) (.leaf (-6))))),
  (.branch 31 (.leaf (-6)) (.leaf (-5))),
  (.branch 25 (.leaf (-4)) (.leaf (-3))),
  (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-3)) (.leaf (0)))),
  (.branch 28 (.branch 16 (.branch 5 (.leaf (-20)) (.leaf (-19))) (.branch 27 (.leaf (-18)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3))))),
  (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-21)) (.leaf (-20))) (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17))))) (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_057_1025 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.leaf (5)))))))
  code := certificateD7_1025
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-24))),
  (.branch 24 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 16 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.branch 22 (.leaf (-7)) (.leaf (-5))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.branch 14 (.branch 11 (.branch 9 (.leaf (-24)) (.branch 10 (.leaf (-23)) (.leaf (-22)))) (.branch 12 (.leaf (-21)) (.branch 13 (.leaf (-20)) (.leaf (-19))))) (.branch 17 (.branch 15 (.leaf (-18)) (.branch 16 (.leaf (-17)) (.leaf (-16)))) (.branch 18 (.leaf (-15)) (.branch 19 (.leaf (-14)) (.leaf (-13)))))) (.branch 26 (.branch 23 (.branch 21 (.leaf (-12)) (.branch 22 (.leaf (-11)) (.leaf (-10)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-13)))) (.branch 22 (.branch 21 (.leaf (-12)) (.leaf (-11))) (.branch 23 (.leaf (-10)) (.leaf (-9))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_057_1026 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1026
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-20))),
  (.branch 28 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 24 (.leaf (-13)) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 22 (.branch 17 (.branch 14 (.branch 13 (.leaf (-20)) (.leaf (-19))) (.branch 15 (.leaf (-18)) (.branch 16 (.leaf (-17)) (.leaf (-16))))) (.branch 19 (.branch 18 (.leaf (-15)) (.leaf (-14))) (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_057_1027 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (1)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1027
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 16 (.leaf (0)) (.leaf (-16))),
  (.leaf (0))]
  high := ![(.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.branch 22 (.leaf (-7)) (.leaf (-5))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-13)))) (.branch 22 (.branch 21 (.leaf (-12)) (.leaf (-11))) (.branch 23 (.leaf (-10)) (.leaf (-9))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_057_1028 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (2))) (.branch 11 (.leaf (6)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (4)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (4)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (3))) (.branch 27 (.leaf (5)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (4)) (.leaf (3)))))))
  code := certificateD7_1028
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-17)) (.leaf (-18)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 27 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-21)))]
  high := ![(.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 26 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 23 (.leaf (-18)) (.leaf (-15))) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.branch 7 (.leaf (-2)) (.branch 20 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-21)) (.leaf (-20))) (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17))))) (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_057_1029 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (2))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (6)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (5)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (3))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1029
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-17)) (.leaf (-18)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 26 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 23 (.leaf (-18)) (.leaf (-15))) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.branch 7 (.leaf (-2)) (.branch 20 (.leaf (-1)) (.leaf (0)))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_057_1030 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (6)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (5)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (4)) (.leaf (3)))))))
  code := certificateD7_1030
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 28 (.leaf (-19)) (.leaf (-20)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 23 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-25)))]
  high := ![(.branch 21 (.leaf (-12)) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-15))) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.branch 13 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 13 (.branch 10 (.branch 8 (.leaf (-25)) (.branch 9 (.leaf (-24)) (.leaf (-23)))) (.branch 11 (.leaf (-22)) (.branch 12 (.leaf (-21)) (.leaf (-20))))) (.branch 16 (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17)))) (.branch 17 (.leaf (-16)) (.branch 18 (.leaf (-15)) (.leaf (-14)))))) (.branch 25 (.branch 22 (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))) (.branch 23 (.leaf (-10)) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_057_1031 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (5))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (6)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (5))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (6)) (.leaf (1)))))))
  code := certificateD7_1031
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.branch 10 (.leaf (-13)) (.leaf (-14))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 18 (.leaf (-5)) (.branch 21 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-23)) (.leaf (-25)))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 27 (.leaf (-14)) (.branch 31 (.leaf (-10)) (.leaf (-5)))),
  (.branch 29 (.branch 22 (.leaf (-7)) (.leaf (-6))) (.branch 30 (.leaf (-3)) (.leaf (0)))),
  (.branch 27 (.branch 25 (.branch 14 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-21)) (.leaf (-18)))) (.branch 29 (.branch 28 (.leaf (-15)) (.leaf (-12))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_057 : Fin 31 → CycleWitness 7 := ![witnessD7_057_1001, witnessD7_057_1002, witnessD7_057_1003, witnessD7_057_1004, witnessD7_057_1005, witnessD7_057_1006, witnessD7_057_1007, witnessD7_057_1008, witnessD7_057_1009, witnessD7_057_1010, witnessD7_057_1011, witnessD7_057_1012, witnessD7_057_1013, witnessD7_057_1014, witnessD7_057_1015, witnessD7_057_1016, witnessD7_057_1017, witnessD7_057_1018, witnessD7_057_1019, witnessD7_057_1020, witnessD7_057_1021, witnessD7_057_1022, witnessD7_057_1023, witnessD7_057_1024, witnessD7_057_1025, witnessD7_057_1026, witnessD7_057_1027, witnessD7_057_1028, witnessD7_057_1029, witnessD7_057_1030, witnessD7_057_1031]
end RealPinwheel.FiveSixths


