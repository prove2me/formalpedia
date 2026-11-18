-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD5_000
-- name    : RealPinwheel_FiveSixths_WitnessD5_000
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T03:55:53.876208+00:00
-- url     : https://prove2.me/theorems/28170e8d-4853-408c-8591-019dc35b67e7
-- title:
--   Exact witness block D5_000
-- statement:
--   These exact witnesses represent words 1 through 36 of source certificate file D5. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D5, entries 1–36; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D5.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD5
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD5_000_0 : CycleWitness 5 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 5 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (3)))))) (.branch 24 (.branch 21 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 29 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (4)))))))
  code := certificateD5_0
  counts := ![(.branch 15 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 10 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 12 (.leaf (7)) (.branch 13 (.leaf (8)) (.leaf (9)))))) (.branch 23 (.branch 18 (.branch 17 (.leaf (10)) (.leaf (11))) (.branch 20 (.leaf (12)) (.branch 21 (.leaf (13)) (.leaf (14))))) (.branch 28 (.branch 25 (.leaf (15)) (.branch 26 (.leaf (16)) (.leaf (17)))) (.branch 29 (.leaf (18)) (.branch 31 (.leaf (19)) (.leaf (20))))))),
  (.branch 14 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 16 (.leaf (0)) (.leaf (-16))),
  (.leaf (0))]
  high := ![(.branch 30 (.leaf (-7)) (.leaf (-5))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-13)))) (.branch 22 (.branch 21 (.leaf (-12)) (.leaf (-11))) (.branch 23 (.leaf (-10)) (.leaf (-9))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD5_000_1 : CycleWitness 5 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (2)) (.leaf (1))))) (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (4)) (.leaf (1)))))))
  code := certificateD5_1
  counts := ![(.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 22 (.branch 18 (.branch 17 (.leaf (8)) (.leaf (9))) (.branch 20 (.leaf (10)) (.leaf (11)))) (.branch 26 (.branch 25 (.leaf (12)) (.leaf (13))) (.branch 28 (.leaf (14)) (.branch 30 (.leaf (15)) (.leaf (16))))))),
  (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 29 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.leaf (12)))))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-17))),
  (.branch 31 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (-17)) (.leaf (-16))) (.branch 18 (.leaf (-15)) (.leaf (-14)))) (.branch 21 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 22 (.leaf (-11)) (.leaf (-10))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD5_000_2 : CycleWitness 5 where
  length := 31
  word := (.branch 16 (.branch 9 (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (3))))) (.branch 24 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (4))))))
  code := certificateD5_2
  counts := ![(.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 6 (.leaf (4)) (.leaf (5))))) (.branch 11 (.branch 8 (.leaf (6)) (.branch 10 (.leaf (7)) (.leaf (8)))) (.branch 13 (.leaf (9)) (.branch 14 (.leaf (10)) (.leaf (11)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (12)) (.branch 18 (.leaf (13)) (.leaf (14)))) (.branch 21 (.leaf (15)) (.branch 22 (.leaf (16)) (.leaf (17))))) (.branch 27 (.branch 25 (.leaf (18)) (.branch 26 (.leaf (19)) (.leaf (20)))) (.branch 29 (.leaf (21)) (.branch 30 (.leaf (22)) (.leaf (23))))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))) (.branch 4 (.leaf (-18)) (.branch 8 (.leaf (-24)) (.leaf (-25))))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.branch 24 (.leaf (-13)) (.leaf (-14)))),
  (.branch 16 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 9 (.leaf (-25)) (.branch 28 (.leaf (-24)) (.leaf (-19)))),
  (.branch 21 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-8)) (.leaf (-4))))),
  (.branch 27 (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-12)) (.leaf (-10)))) (.branch 29 (.branch 28 (.leaf (-8)) (.leaf (-6))) (.branch 30 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.branch 19 (.branch 17 (.leaf (-15)) (.branch 18 (.leaf (-14)) (.leaf (-13)))) (.branch 21 (.branch 20 (.leaf (-12)) (.leaf (-11))) (.branch 22 (.leaf (-10)) (.leaf (-9))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-7))) (.branch 26 (.leaf (-6)) (.leaf (-5)))) (.branch 29 (.branch 28 (.leaf (-4)) (.leaf (-3))) (.branch 30 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD5_000_3 : CycleWitness 5 where
  length := 30
  word := (.branch 15 (.branch 9 (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 25 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (4))))))
  code := certificateD5_3
  counts := ![(.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 6 (.leaf (4)) (.leaf (5))))) (.branch 11 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (7)) (.leaf (8)))) (.branch 12 (.leaf (9)) (.branch 13 (.leaf (10)) (.leaf (11)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (12)) (.branch 17 (.leaf (13)) (.leaf (14)))) (.branch 19 (.leaf (15)) (.branch 21 (.leaf (16)) (.leaf (17))))) (.branch 26 (.branch 23 (.leaf (18)) (.branch 24 (.leaf (19)) (.leaf (20)))) (.branch 28 (.branch 27 (.leaf (21)) (.leaf (22))) (.branch 29 (.leaf (23)) (.leaf (24))))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-1))) (.branch 3 (.leaf (-2)) (.branch 4 (.leaf (-3)) (.leaf (-4))))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-20))),
  (.branch 20 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.leaf (-4)),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.branch 15 (.branch 12 (.branch 11 (.leaf (-20)) (.leaf (-19))) (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16))))) (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD5_000_4 : CycleWitness 5 where
  length := 30
  word := (.branch 16 (.branch 8 (.branch 5 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 20 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (1))))) (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (4)) (.branch 29 (.leaf (0)) (.leaf (1)))))))
  code := certificateD5_4
  counts := ![(.branch 14 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))))) (.branch 22 (.branch 17 (.branch 15 (.leaf (9)) (.leaf (10))) (.branch 19 (.leaf (11)) (.branch 21 (.leaf (12)) (.leaf (13))))) (.branch 25 (.branch 24 (.leaf (14)) (.leaf (15))) (.branch 27 (.leaf (16)) (.branch 29 (.leaf (17)) (.leaf (18))))))),
  (.branch 16 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-22))),
  (.branch 18 (.leaf (0)) (.leaf (-12))),
  (.branch 28 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 26 (.leaf (-5)) (.branch 28 (.leaf (-4)) (.leaf (-3)))),
  (.branch 27 (.leaf (-2)) (.leaf (0))),
  (.branch 19 (.branch 13 (.branch 10 (.branch 9 (.leaf (-22)) (.leaf (-21))) (.branch 11 (.leaf (-20)) (.branch 12 (.leaf (-19)) (.leaf (-18))))) (.branch 16 (.branch 14 (.leaf (-17)) (.branch 15 (.leaf (-16)) (.leaf (-15)))) (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1)))]
def witnessD5_000_5 : CycleWitness 5 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (3)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (1)))))))
  code := certificateD5_5
  counts := ![(.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.branch 29 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 5 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 22 (.leaf (0)) (.leaf (-8))),
  (.branch 7 (.leaf (0)) (.leaf (-23)))]
  high := ![(.branch 22 (.branch 3 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))) (.branch 26 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))),
  (.branch 27 (.leaf (-1)) (.leaf (0))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-23)) (.leaf (-22))) (.branch 10 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19))))) (.branch 15 (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD5_000_6 : CycleWitness 5 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (2))) (.branch 22 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (1)))))))
  code := certificateD5_6
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 17 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 19 (.leaf (9)) (.leaf (10)))) (.branch 26 (.branch 24 (.leaf (11)) (.leaf (12))) (.branch 28 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 5 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 18 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))) (.branch 17 (.leaf (-13)) (.branch 19 (.leaf (-14)) (.leaf (-15))))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 20 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-9)))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.branch 20 (.branch 15 (.branch 12 (.branch 11 (.leaf (-20)) (.leaf (-19))) (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16))))) (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_000_7 : CycleWitness 5 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (4)) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (1)))))))
  code := certificateD5_7
  counts := ![(.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.branch 29 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-21))),
  (.branch 24 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 22 (.branch 18 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))) (.branch 26 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))),
  (.branch 23 (.branch 19 (.leaf (-3)) (.leaf (-2))) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 21 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-21)) (.leaf (-20))) (.branch 12 (.leaf (-19)) (.branch 13 (.leaf (-18)) (.leaf (-17))))) (.branch 16 (.branch 15 (.leaf (-16)) (.leaf (-15))) (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_000_8 : CycleWitness 5 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (4)) (.leaf (0))) (.branch 22 (.leaf (3)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (3)))))))
  code := certificateD5_8
  counts := ![(.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.branch 29 (.leaf (15)) (.leaf (16))))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 22 (.branch 18 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))) (.branch 26 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 27 (.branch 16 (.leaf (-12)) (.leaf (-11))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-7)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD5_000_9 : CycleWitness 5 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (2)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (4))) (.branch 22 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (1)) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (1)))))))
  code := certificateD5_9
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 26 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 18 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 17 (.leaf (-10)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-24))),
  (.branch 21 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 18 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-9)))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 18 (.branch 12 (.branch 9 (.branch 7 (.leaf (-24)) (.branch 8 (.leaf (-23)) (.leaf (-22)))) (.branch 10 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19))))) (.branch 15 (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD5_000_10 : CycleWitness 5 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (4))))))
  code := certificateD5_10
  counts := ![(.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 8 (.leaf (5)) (.leaf (6))) (.branch 10 (.leaf (7)) (.branch 12 (.leaf (8)) (.leaf (9)))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (10)) (.leaf (11))) (.branch 17 (.leaf (12)) (.branch 19 (.leaf (13)) (.leaf (14))))) (.branch 24 (.branch 22 (.leaf (15)) (.branch 23 (.leaf (16)) (.leaf (17)))) (.branch 26 (.leaf (18)) (.branch 27 (.leaf (19)) (.leaf (20))))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 3 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 25 (.leaf (-6)) (.leaf (-5))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 17 (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))) (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.leaf (-8))))) (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD5_000_11 : CycleWitness 5 where
  length := 28
  word := (.branch 14 (.branch 8 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 22 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (4)))))))
  code := certificateD5_11
  counts := ![(.branch 13 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))))) (.branch 21 (.branch 16 (.branch 15 (.leaf (9)) (.leaf (10))) (.branch 18 (.leaf (11)) (.branch 19 (.leaf (12)) (.leaf (13))))) (.branch 24 (.branch 22 (.leaf (14)) (.leaf (15))) (.branch 26 (.leaf (16)) (.branch 27 (.leaf (17)) (.leaf (18))))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-10)) (.branch 8 (.leaf (-11)) (.leaf (-12))))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (-2))) (.branch 25 (.leaf (-5)) (.leaf (-7)))),
  (.branch 14 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 23 (.leaf (-12)) (.leaf (-9))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))),
  (.branch 21 (.branch 17 (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))) (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.leaf (-8))))) (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD5_000_12 : CycleWitness 5 where
  length := 28
  word := (.branch 14 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (4)) (.leaf (0)))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (1)))))))
  code := certificateD5_12
  counts := ![(.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 18 (.leaf (10)) (.leaf (11)))) (.branch 23 (.branch 21 (.leaf (12)) (.leaf (13))) (.branch 25 (.leaf (14)) (.branch 27 (.leaf (15)) (.leaf (16))))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 7 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-18))),
  (.branch 24 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 24 (.branch 22 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 24 (.branch 23 (.leaf (-3)) (.leaf (-2))) (.branch 25 (.leaf (-1)) (.leaf (0)))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.branch 14 (.branch 12 (.branch 11 (.leaf (-18)) (.leaf (-17))) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 16 (.branch 15 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_000_13 : CycleWitness 5 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (0)))) (.branch 26 (.leaf (4)) (.branch 27 (.leaf (0)) (.leaf (1)))))))
  code := certificateD5_13
  counts := ![(.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 18 (.leaf (10)) (.leaf (11)))) (.branch 23 (.branch 22 (.leaf (12)) (.leaf (13))) (.branch 25 (.leaf (14)) (.branch 27 (.leaf (15)) (.leaf (16))))))),
  (.branch 14 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-16))),
  (.branch 26 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 24 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 25 (.leaf (-1)) (.leaf (0))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 16 (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1)))]
def witnessD5_000_14 : CycleWitness 5 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2)))))))
  code := certificateD5_14
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (7)) (.leaf (8))) (.branch 18 (.leaf (9)) (.leaf (10)))) (.branch 24 (.branch 22 (.leaf (11)) (.leaf (12))) (.branch 27 (.leaf (13)) (.leaf (14)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-5)) (.leaf (-7)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 25 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-17)) (.leaf (-16))) (.branch 14 (.leaf (-15)) (.leaf (-14)))) (.branch 17 (.branch 16 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-11)) (.leaf (-10))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_000_15 : CycleWitness 5 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (4)))))))
  code := certificateD5_15
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 25 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.leaf (12)))))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-1))) (.branch 6 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 27 (.leaf (-6)) (.leaf (-3))),
  (.leaf (-3)),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 17 (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))) (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.leaf (-8))))) (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD5_000_16 : CycleWitness 5 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (3)))))))
  code := certificateD5_16
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 16 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-4)) (.leaf (-8)))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 22 (.leaf (-6)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 21 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 22 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))),
  (.branch 25 (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3))))),
  (.branch 9 (.leaf (-2)) (.branch 20 (.leaf (-1)) (.leaf (0)))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_000_17 : CycleWitness 5 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (2)))))))
  code := certificateD5_17
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 24 (.branch 21 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.branch 7 (.leaf (-6)) (.leaf (-7))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 22 (.leaf (-2)) (.leaf (-3)))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 25 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 22 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.leaf (-3)) (.leaf (-2))),
  (.branch 24 (.branch 23 (.leaf (-3)) (.leaf (-2))) (.branch 25 (.leaf (-1)) (.leaf (0)))),
  (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-17)) (.leaf (-16))) (.branch 14 (.leaf (-15)) (.leaf (-14)))) (.branch 17 (.branch 16 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-11)) (.leaf (-10))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_000_18 : CycleWitness 5 where
  length := 28
  word := (.branch 14 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (4)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 26 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2)))))))
  code := certificateD5_18
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 26 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 21 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 20 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-3)))),
  (.branch 27 (.leaf (-6)) (.leaf (-5))),
  (.branch 19 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 10 (.leaf (-19)) (.branch 11 (.leaf (-18)) (.leaf (-17))))) (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_000_19 : CycleWitness 5 where
  length := 27
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2)))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.leaf (0))) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (0)) (.leaf (1)))))))
  code := certificateD5_19
  counts := ![(.branch 12 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 8 (.branch 6 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (8)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (9)) (.leaf (10))) (.branch 17 (.leaf (11)) (.branch 19 (.leaf (12)) (.leaf (13))))) (.branch 23 (.branch 21 (.leaf (14)) (.leaf (15))) (.branch 24 (.leaf (16)) (.branch 26 (.leaf (17)) (.leaf (18))))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-1))) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-20))),
  (.branch 15 (.leaf (0)) (.leaf (-12))),
  (.branch 25 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-20)) (.leaf (-19))) (.branch 10 (.leaf (-18)) (.branch 11 (.leaf (-17)) (.leaf (-16))))) (.branch 14 (.branch 13 (.leaf (-15)) (.leaf (-14))) (.branch 15 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-11)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-10)) (.leaf (-9))) (.branch 20 (.leaf (-8)) (.branch 21 (.leaf (-7)) (.leaf (-6))))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 18 (.branch 16 (.leaf (-12)) (.branch 17 (.leaf (-11)) (.leaf (-10)))) (.branch 19 (.leaf (-9)) (.branch 20 (.leaf (-8)) (.leaf (-7))))) (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.leaf (-2)) (.leaf (-1)))]
def witnessD5_000_20 : CycleWitness 5 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (2)))))))
  code := certificateD5_20
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (7)) (.leaf (8))) (.branch 17 (.leaf (9)) (.leaf (10)))) (.branch 23 (.branch 21 (.leaf (11)) (.leaf (12))) (.branch 25 (.leaf (13)) (.leaf (14)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 5 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 18 (.leaf (-5)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 24 (.leaf (-8)) (.leaf (-7))))),
  (.branch 19 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 12 (.leaf (-15)) (.leaf (-14)))) (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_000_21 : CycleWitness 5 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (0))) (.branch 23 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (2)))))))
  code := certificateD5_21
  counts := ![(.branch 12 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (8)) (.leaf (9))) (.branch 17 (.leaf (10)) (.leaf (11)))) (.branch 22 (.branch 20 (.leaf (12)) (.leaf (13))) (.branch 24 (.leaf (14)) (.branch 25 (.leaf (15)) (.leaf (16))))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 16 (.leaf (-10)) (.branch 21 (.leaf (-9)) (.leaf (-8)))),
  (.branch 24 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 20 (.branch 19 (.leaf (-3)) (.leaf (-2))) (.branch 21 (.leaf (-1)) (.leaf (0)))),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_000_22 : CycleWitness 5 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (4))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (1)))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))))))
  code := certificateD5_22
  counts := ![(.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 14 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 15 (.leaf (-14)) (.leaf (-17)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 12 (.leaf (-2)) (.branch 25 (.leaf (-4)) (.leaf (-5))))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 19 (.branch 16 (.leaf (-17)) (.leaf (-16))) (.branch 22 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-10))))),
  (.leaf (-5)),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.branch 11 (.branch 9 (.branch 8 (.leaf (-19)) (.leaf (-18))) (.branch 10 (.leaf (-17)) (.leaf (-16)))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_000_23 : CycleWitness 5 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (1)))))))
  code := certificateD5_23
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 17 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 22 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 21 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.leaf (0)))),
  (.branch 19 (.leaf (-3)) (.leaf (-2))),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 12 (.leaf (-15)) (.leaf (-14)))) (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_000_24 : CycleWitness 5 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (2)))))))
  code := certificateD5_24
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-8)) (.leaf (-11)))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 17 (.leaf (-6)) (.leaf (-8)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 17 (.leaf (-11)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 18 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6)))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.branch 11 (.branch 9 (.branch 8 (.leaf (-19)) (.leaf (-18))) (.branch 10 (.leaf (-17)) (.leaf (-16)))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_000_25 : CycleWitness 5 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (4)))))))
  code := certificateD5_25
  counts := ![(.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 22 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 24 (.leaf (11)) (.leaf (12)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-8)))) (.branch 9 (.branch 7 (.leaf (-9)) (.leaf (-10))) (.branch 11 (.leaf (-11)) (.leaf (-12))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 25 (.leaf (-12)) (.leaf (-6))),
  (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD5_000_26 : CycleWitness 5 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (2)))))))
  code := certificateD5_26
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 17 (.leaf (-14)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 22 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 24 (.branch 18 (.leaf (-16)) (.leaf (-13))) (.branch 25 (.leaf (-9)) (.leaf (-5)))),
  (.branch 5 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (0)))),
  (.branch 19 (.leaf (-3)) (.leaf (-2))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_000_27 : CycleWitness 5 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (4)))))))
  code := certificateD5_27
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 8 (.leaf (-6)) (.branch 11 (.leaf (-7)) (.leaf (-8))))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 9 (.leaf (-2)) (.branch 12 (.leaf (-3)) (.leaf (-4))))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 25 (.leaf (-8)) (.leaf (-4))),
  (.leaf (-4)),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD5_000_28 : CycleWitness 5 where
  length := 25
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (4)) (.leaf (1)))))))
  code := certificateD5_28
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 12 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 21 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 23 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 5 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 16 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 25 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 4 (.leaf (-14)) (.branch 12 (.leaf (-15)) (.leaf (-19))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 20 (.leaf (-2)) (.branch 22 (.leaf (-4)) (.leaf (-8))))),
  (.branch 14 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.leaf (-19))),
  (.branch 24 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 13 (.leaf (-19)) (.branch 24 (.leaf (-18)) (.leaf (-12)))),
  (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 19 (.branch 16 (.branch 15 (.leaf (-11)) (.leaf (-10))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-8)) (.leaf (-7))))) (.branch 22 (.branch 20 (.leaf (-6)) (.branch 21 (.leaf (-5)) (.leaf (-4)))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 10 (.branch 8 (.branch 7 (.leaf (-19)) (.leaf (-18))) (.branch 9 (.leaf (-17)) (.leaf (-16)))) (.branch 12 (.branch 11 (.leaf (-15)) (.leaf (-14))) (.branch 13 (.leaf (-13)) (.branch 14 (.leaf (-12)) (.leaf (-11)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-10)) (.leaf (-9))) (.branch 18 (.leaf (-8)) (.branch 19 (.leaf (-7)) (.leaf (-6))))) (.branch 22 (.branch 21 (.leaf (-5)) (.leaf (-4))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD5_000_29 : CycleWitness 5 where
  length := 25
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 7 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (0)))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 23 (.leaf (1)) (.branch 24 (.leaf (0)) (.leaf (4)))))))
  code := certificateD5_29
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (7)) (.leaf (8))) (.branch 17 (.leaf (9)) (.leaf (10)))) (.branch 22 (.branch 20 (.leaf (11)) (.leaf (12))) (.branch 24 (.leaf (13)) (.leaf (14)))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 9 (.leaf (-22)) (.leaf (-24)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-7)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0))]
  high := ![(.branch 19 (.branch 10 (.leaf (-24)) (.leaf (-23))) (.branch 21 (.leaf (-20)) (.branch 23 (.leaf (-17)) (.leaf (-14))))),
  (.branch 17 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-8)))),
  (.branch 22 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))),
  (.branch 22 (.branch 20 (.leaf (-12)) (.branch 21 (.leaf (-10)) (.leaf (-8)))) (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD5_000_30 : CycleWitness 5 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (4)))))
  code := certificateD5_30
  counts := ![(.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (4))))) (.branch 8 (.branch 7 (.leaf (5)) (.leaf (6))) (.branch 9 (.leaf (7)) (.branch 10 (.leaf (8)) (.leaf (9)))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (10)) (.leaf (11))) (.branch 15 (.leaf (12)) (.branch 16 (.leaf (13)) (.leaf (14))))) (.branch 21 (.branch 19 (.leaf (15)) (.branch 20 (.leaf (16)) (.leaf (17)))) (.branch 22 (.leaf (18)) (.branch 23 (.leaf (19)) (.leaf (20))))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))) (.branch 4 (.leaf (-3)) (.branch 5 (.leaf (-4)) (.leaf (-5))))),
  (.branch 6 (.leaf (0)) (.leaf (-18))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.leaf (-5)),
  (.branch 15 (.branch 10 (.branch 8 (.branch 7 (.leaf (-18)) (.leaf (-17))) (.branch 9 (.leaf (-16)) (.leaf (-15)))) (.branch 12 (.branch 11 (.leaf (-14)) (.leaf (-13))) (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 18 (.branch 15 (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))) (.branch 16 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7))))) (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_000_31 : CycleWitness 5 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.leaf (2)))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (4))))))
  code := certificateD5_31
  counts := ![(.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.leaf (7))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (8)) (.leaf (9))) (.branch 16 (.leaf (10)) (.leaf (11)))) (.branch 20 (.branch 19 (.leaf (12)) (.leaf (13))) (.branch 22 (.leaf (14)) (.branch 23 (.leaf (15)) (.leaf (16))))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.leaf (-2)),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 15 (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))) (.branch 16 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7))))) (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD5_000_32 : CycleWitness 5 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (1)))))))
  code := certificateD5_32
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 13 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 20 (.leaf (9)) (.branch 23 (.leaf (10)) (.leaf (11)))))),
  (.branch 12 (.branch 5 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 4 (.leaf (-10)) (.leaf (-11)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-10))),
  (.branch 21 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-18)))]
  high := ![(.branch 14 (.leaf (-11)) (.branch 21 (.leaf (-10)) (.leaf (-7)))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 19 (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.branch 18 (.leaf (-7)) (.leaf (-6))))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 10 (.branch 8 (.branch 7 (.leaf (-18)) (.leaf (-17))) (.branch 9 (.leaf (-16)) (.leaf (-15)))) (.branch 12 (.branch 11 (.leaf (-14)) (.leaf (-13))) (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD5_000_33 : CycleWitness 5 where
  length := 24
  word := (.branch 12 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (0)) (.leaf (1)))))))
  code := certificateD5_33
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 14 (.branch 13 (.leaf (7)) (.leaf (8))) (.branch 16 (.leaf (9)) (.leaf (10)))) (.branch 21 (.branch 19 (.leaf (11)) (.leaf (12))) (.branch 23 (.leaf (13)) (.leaf (14)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-14))),
  (.branch 22 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 20 (.leaf (-11)) (.branch 22 (.leaf (-9)) (.leaf (-7)))),
  (.branch 16 (.leaf (-1)) (.leaf (0))),
  (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 13 (.branch 11 (.leaf (-14)) (.branch 12 (.leaf (-13)) (.leaf (-12)))) (.branch 15 (.branch 14 (.leaf (-11)) (.leaf (-10))) (.branch 16 (.leaf (-9)) (.leaf (-8))))) (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1)))]
def witnessD5_000_34 : CycleWitness 5 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (1)))))))
  code := certificateD5_34
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 16 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))) (.branch 20 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 22 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 16 (.branch 12 (.branch 10 (.leaf (-15)) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_000_35 : CycleWitness 5 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (3)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1))))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (1)))))))
  code := certificateD5_35
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 16 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))) (.branch 20 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 22 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-13))),
  (.branch 23 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 14 (.branch 12 (.leaf (-13)) (.branch 13 (.leaf (-12)) (.leaf (-11)))) (.branch 15 (.leaf (-10)) (.branch 16 (.leaf (-9)) (.leaf (-8))))) (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD5_000 : Fin 36 → CycleWitness 5 := ![witnessD5_000_0, witnessD5_000_1, witnessD5_000_2, witnessD5_000_3, witnessD5_000_4, witnessD5_000_5, witnessD5_000_6, witnessD5_000_7, witnessD5_000_8, witnessD5_000_9, witnessD5_000_10, witnessD5_000_11, witnessD5_000_12, witnessD5_000_13, witnessD5_000_14, witnessD5_000_15, witnessD5_000_16, witnessD5_000_17, witnessD5_000_18, witnessD5_000_19, witnessD5_000_20, witnessD5_000_21, witnessD5_000_22, witnessD5_000_23, witnessD5_000_24, witnessD5_000_25, witnessD5_000_26, witnessD5_000_27, witnessD5_000_28, witnessD5_000_29, witnessD5_000_30, witnessD5_000_31, witnessD5_000_32, witnessD5_000_33, witnessD5_000_34, witnessD5_000_35]
end RealPinwheel.FiveSixths


