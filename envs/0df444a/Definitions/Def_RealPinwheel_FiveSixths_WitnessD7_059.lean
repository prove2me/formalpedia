-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_059
-- name    : RealPinwheel_FiveSixths_WitnessD7_059
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:05:35.557428+00:00
-- url     : https://prove2.me/theorems/31394ec6-11e6-42ab-a920-de1a484b6b3a
-- title:
--   Exact witness block D7_059
-- statement:
--   These exact witnesses represent words 1064 through 1095 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 1064–1095; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_059_1063 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (6))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (3))) (.branch 19 (.leaf (1)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (0))) (.branch 23 (.leaf (4)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (6))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (1))) (.branch 31 (.leaf (3)) (.leaf (4)))))))
  code := certificateD7_1063
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-22)) (.leaf (-24)))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 29 (.branch 28 (.leaf (-15)) (.leaf (-12))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-6)) (.leaf (-3))))),
  (.branch 20 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.branch 9 (.leaf (-24)) (.branch 22 (.leaf (-23)) (.leaf (-20)))) (.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-10)) (.leaf (-5))))),
  (.branch 25 (.leaf (-8)) (.leaf (-5))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 30 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_059_1064 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (5)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (3)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (4)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (3)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (6)) (.leaf (1)))))))
  code := certificateD7_1064
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-17))),
  (.branch 31 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (-17)) (.leaf (-16))) (.branch 18 (.leaf (-15)) (.leaf (-14)))) (.branch 21 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 22 (.leaf (-11)) (.leaf (-10))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_059_1065 : CycleWitness 7 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (5)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (1))) (.branch 23 (.leaf (4)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (2))) (.branch 27 (.leaf (1)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1065
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-25))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 25 (.branch 2 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-21)) (.branch 31 (.leaf (-14)) (.leaf (-7))))),
  (.branch 18 (.leaf (-9)) (.leaf (-7))),
  (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 29 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_059_1066 : CycleWitness 7 where
  length := 31
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 19 (.branch 16 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (1))))) (.branch 27 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 29 (.branch 28 (.leaf (1)) (.leaf (6))) (.branch 30 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1066
  counts := ![(.branch 14 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 23 (.branch 18 (.branch 17 (.leaf (8)) (.leaf (9))) (.branch 20 (.leaf (10)) (.leaf (11)))) (.branch 26 (.branch 24 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.branch 30 (.leaf (15)) (.leaf (16))))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-1))) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-16)) (.leaf (-17)))),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 10 (.leaf (0)) (.branch 19 (.leaf (-1)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (-19)) (.leaf (-20)))),
  (.branch 13 (.leaf (0)) (.leaf (-18))),
  (.branch 29 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 28 (.leaf (-3)) (.leaf (-2))),
  (.branch 29 (.branch 10 (.leaf (-17)) (.leaf (-15))) (.branch 30 (.leaf (-10)) (.leaf (-5)))),
  (.branch 27 (.branch 5 (.leaf (-19)) (.branch 26 (.leaf (-18)) (.leaf (-15)))) (.branch 29 (.branch 28 (.leaf (-12)) (.leaf (-9))) (.branch 30 (.leaf (-6)) (.leaf (-3))))),
  (.branch 21 (.branch 20 (.leaf (-3)) (.leaf (-2))) (.branch 22 (.leaf (-1)) (.leaf (0)))),
  (.branch 26 (.branch 23 (.branch 22 (.leaf (-20)) (.leaf (-18))) (.branch 24 (.leaf (-16)) (.branch 25 (.leaf (-14)) (.leaf (-12))))) (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-8))) (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-18)) (.leaf (-17))) (.branch 16 (.leaf (-16)) (.leaf (-15)))) (.branch 19 (.branch 18 (.leaf (-14)) (.leaf (-13))) (.branch 20 (.leaf (-12)) (.branch 21 (.leaf (-11)) (.leaf (-10)))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (-9)) (.leaf (-8))) (.branch 25 (.leaf (-7)) (.leaf (-6)))) (.branch 28 (.branch 27 (.leaf (-5)) (.leaf (-4))) (.branch 29 (.leaf (-3)) (.branch 30 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_059_1067 : CycleWitness 7 where
  length := 31
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (5))) (.branch 15 (.leaf (2)) (.leaf (0)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 21 (.branch 20 (.leaf (3)) (.leaf (0))) (.branch 22 (.leaf (5)) (.leaf (2))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (0)) (.leaf (1)))) (.branch 29 (.branch 28 (.leaf (6)) (.leaf (0))) (.branch 30 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1067
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 26 (.branch 24 (.leaf (9)) (.leaf (10))) (.branch 29 (.leaf (11)) (.leaf (12)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-18)) (.leaf (-36)))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (-5)) (.leaf (-8)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 22 (.leaf (-10)) (.leaf (-14)))),
  (.branch 12 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 19 (.branch 3 (.leaf (-36)) (.branch 11 (.leaf (-35)) (.leaf (-34)))) (.branch 27 (.leaf (-33)) (.branch 30 (.leaf (-29)) (.leaf (-18))))),
  (.branch 20 (.branch 4 (.leaf (-19)) (.branch 12 (.leaf (-18)) (.leaf (-17)))) (.branch 29 (.branch 28 (.leaf (-16)) (.leaf (-12))) (.branch 30 (.leaf (-8)) (.leaf (-4))))),
  (.branch 16 (.branch 8 (.leaf (-3)) (.leaf (-2))) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 10 (.leaf (-4)) (.leaf (-3))),
  (.branch 28 (.branch 26 (.leaf (-8)) (.branch 27 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.leaf (-5)) (.branch 30 (.leaf (-4)) (.leaf (-3))))),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-14)) (.leaf (-13))) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 29 (.branch 13 (.leaf (-7)) (.leaf (-6))) (.branch 30 (.leaf (-4)) (.leaf (-2))))]
def witnessD7_059_1068 : CycleWitness 7 where
  length := 31
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (4)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (3)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (6)) (.leaf (4)))) (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1068
  counts := ![(.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 6 (.leaf (-23)) (.leaf (-24)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (-7)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.leaf (-20))),
  (.branch 26 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 26 (.branch 7 (.leaf (-24)) (.leaf (-23))) (.branch 30 (.leaf (-17)) (.leaf (-10)))),
  (.branch 29 (.leaf (-4)) (.branch 30 (.leaf (-3)) (.leaf (-2)))),
  (.branch 16 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 21 (.leaf (-7)) (.leaf (-6))),
  (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-7))) (.branch 30 (.leaf (-5)) (.leaf (-3)))),
  (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-20)) (.leaf (-19))) (.branch 14 (.leaf (-18)) (.branch 15 (.leaf (-17)) (.leaf (-16))))) (.branch 18 (.branch 17 (.leaf (-15)) (.leaf (-14))) (.branch 19 (.leaf (-13)) (.branch 20 (.leaf (-12)) (.leaf (-11)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-9))) (.branch 24 (.leaf (-8)) (.branch 25 (.leaf (-7)) (.leaf (-6))))) (.branch 28 (.branch 27 (.leaf (-5)) (.leaf (-4))) (.branch 29 (.leaf (-3)) (.branch 30 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 27 (.leaf (-5)) (.leaf (-4))) (.branch 29 (.leaf (-3)) (.branch 30 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_059_1069 : CycleWitness 7 where
  length := 31
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (4)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (6))) (.branch 14 (.leaf (0)) (.leaf (3)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (2)) (.leaf (0))) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (5)) (.leaf (0))) (.branch 22 (.leaf (1)) (.leaf (2))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (4)) (.leaf (0)))) (.branch 29 (.branch 28 (.leaf (1)) (.leaf (6))) (.branch 30 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1069
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 27 (.branch 24 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 21 (.leaf (-7)) (.leaf (-9)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-16))) (.branch 12 (.leaf (-17)) (.branch 22 (.leaf (-18)) (.leaf (-20))))),
  (.branch 23 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 10 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (-21)) (.leaf (-22)))),
  (.branch 13 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 25 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))),
  (.branch 29 (.branch 23 (.leaf (-20)) (.leaf (-16))) (.branch 30 (.leaf (-11)) (.leaf (-6)))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 5 (.leaf (-19)) (.branch 26 (.leaf (-18)) (.leaf (-15)))) (.branch 29 (.branch 28 (.leaf (-12)) (.leaf (-9))) (.branch 30 (.leaf (-6)) (.leaf (-3))))),
  (.branch 28 (.branch 11 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-8)))) (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-4)) (.leaf (-2))))),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-22)) (.leaf (-20))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-16)) (.leaf (-14))))) (.branch 28 (.branch 26 (.leaf (-12)) (.branch 27 (.leaf (-10)) (.leaf (-8)))) (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 14 (.leaf (-5)) (.branch 30 (.leaf (-4)) (.leaf (-2))))]
def witnessD7_059_1070 : CycleWitness 7 where
  length := 31
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (6)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (5)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (4)) (.leaf (3)))) (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1070
  counts := ![(.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 6 (.leaf (-23)) (.leaf (-24)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (-7)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.branch 26 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-23))),
  (.branch 14 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 26 (.branch 7 (.leaf (-24)) (.leaf (-23))) (.branch 30 (.leaf (-17)) (.leaf (-10)))),
  (.branch 29 (.leaf (-4)) (.branch 30 (.leaf (-3)) (.leaf (-2)))),
  (.branch 16 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-7))) (.branch 30 (.leaf (-5)) (.leaf (-3)))),
  (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-8))) (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-4)) (.leaf (-2))))),
  (.branch 25 (.branch 22 (.branch 5 (.leaf (-23)) (.branch 21 (.leaf (-22)) (.leaf (-20)))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-16)) (.leaf (-14))))) (.branch 28 (.branch 26 (.leaf (-12)) (.branch 27 (.leaf (-10)) (.leaf (-8)))) (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 15 (.leaf (-3)) (.leaf (-2)))]
def witnessD7_059_1071 : CycleWitness 7 where
  length := 31
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (3)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (6))) (.branch 14 (.leaf (2)) (.leaf (5)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (4)) (.leaf (2)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (3))) (.branch 22 (.leaf (1)) (.leaf (5))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (4)) (.leaf (1)))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (6))) (.branch 30 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1071
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-23)) (.leaf (-30)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-18)) (.leaf (-19)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (-4)) (.leaf (-7)))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 23 (.leaf (-9)) (.leaf (-13)))),
  (.branch 13 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 17 (.branch 9 (.branch 5 (.leaf (-30)) (.leaf (-29))) (.branch 13 (.leaf (-28)) (.leaf (-27)))) (.branch 25 (.branch 21 (.leaf (-26)) (.leaf (-25))) (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-16)) (.leaf (-8)))))),
  (.branch 28 (.branch 12 (.leaf (-19)) (.leaf (-18))) (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-10)) (.leaf (-6))))),
  (.branch 4 (.leaf (-9)) (.branch 20 (.leaf (-8)) (.leaf (-6)))),
  (.branch 11 (.leaf (-1)) (.leaf (0))),
  (.branch 28 (.branch 27 (.leaf (-7)) (.leaf (-6))) (.branch 29 (.leaf (-5)) (.branch 30 (.leaf (-4)) (.leaf (-3))))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-13)) (.leaf (-12))) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6))))),
  (.branch 14 (.leaf (-5)) (.branch 30 (.leaf (-4)) (.leaf (-2))))]
def witnessD7_059_1072 : CycleWitness 7 where
  length := 31
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (2))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (4)) (.leaf (0)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (2)) (.leaf (0))) (.branch 18 (.leaf (1)) (.leaf (3)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (4)) (.leaf (1))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (6))) (.branch 26 (.leaf (0)) (.leaf (3)))) (.branch 29 (.branch 28 (.leaf (2)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1072
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (-5)) (.leaf (-7)))) (.branch 20 (.leaf (-8)) (.branch 26 (.leaf (-9)) (.leaf (-11))))),
  (.branch 2 (.leaf (0)) (.leaf (-16))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 21 (.leaf (-14)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-17)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-21))),
  (.branch 25 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 27 (.leaf (-11)) (.leaf (-10))),
  (.branch 24 (.branch 3 (.leaf (-16)) (.leaf (-15))) (.branch 30 (.leaf (-11)) (.leaf (-6)))),
  (.branch 29 (.branch 22 (.leaf (-16)) (.leaf (-13))) (.branch 30 (.leaf (-9)) (.leaf (-5)))),
  (.branch 28 (.branch 20 (.leaf (-17)) (.leaf (-16))) (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-8)) (.leaf (-4))))),
  (.branch 23 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 20 (.branch 15 (.branch 12 (.branch 11 (.leaf (-21)) (.leaf (-20))) (.branch 13 (.leaf (-19)) (.branch 14 (.leaf (-18)) (.leaf (-17))))) (.branch 17 (.branch 16 (.leaf (-16)) (.leaf (-15))) (.branch 18 (.leaf (-14)) (.branch 19 (.leaf (-13)) (.leaf (-12)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-11)) (.leaf (-10))) (.branch 23 (.leaf (-9)) (.branch 24 (.leaf (-8)) (.leaf (-7))))) (.branch 28 (.branch 26 (.leaf (-6)) (.branch 27 (.leaf (-5)) (.leaf (-4)))) (.branch 29 (.leaf (-3)) (.branch 30 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 26 (.leaf (-6)) (.branch 27 (.leaf (-5)) (.leaf (-4)))) (.branch 29 (.leaf (-3)) (.branch 30 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_059_1073 : CycleWitness 7 where
  length := 31
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (2))) (.branch 10 (.leaf (4)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (6)) (.leaf (0)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (2)) (.leaf (0))) (.branch 18 (.leaf (1)) (.leaf (3)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (5)) (.leaf (1))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (0)) (.leaf (3)))) (.branch 29 (.branch 28 (.leaf (2)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1073
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (-5)) (.leaf (-7)))) (.branch 20 (.leaf (-8)) (.branch 26 (.leaf (-9)) (.leaf (-11))))),
  (.branch 2 (.leaf (0)) (.leaf (-16))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 21 (.leaf (-14)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-17)))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.leaf (-19))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 27 (.leaf (-11)) (.leaf (-10))),
  (.branch 24 (.branch 3 (.leaf (-16)) (.leaf (-15))) (.branch 30 (.leaf (-11)) (.leaf (-6)))),
  (.branch 29 (.branch 22 (.leaf (-16)) (.leaf (-13))) (.branch 30 (.leaf (-9)) (.leaf (-5)))),
  (.branch 28 (.branch 20 (.leaf (-17)) (.leaf (-16))) (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-8)) (.leaf (-4))))),
  (.branch 28 (.branch 26 (.leaf (-12)) (.branch 27 (.leaf (-10)) (.leaf (-8)))) (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-4)) (.leaf (-2))))),
  (.branch 26 (.branch 23 (.branch 7 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-16)) (.branch 25 (.leaf (-14)) (.leaf (-12))))) (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-8))) (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 15 (.leaf (-2)) (.branch 16 (.leaf (-1)) (.leaf (0))))]
def witnessD7_059_1074 : CycleWitness 7 where
  length := 31
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (5)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (3)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (5)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (6))) (.branch 22 (.leaf (1)) (.leaf (3))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (2)) (.leaf (1)))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (5))) (.branch 30 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1074
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-23)) (.leaf (-27)))),
  (.branch 2 (.leaf (0)) (.branch 30 (.leaf (-14)) (.leaf (-18)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-19)) (.leaf (-21)))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-19)) (.leaf (-20)))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (-1))) (.branch 29 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (-19)) (.leaf (-20))))]
  high := ![(.branch 25 (.branch 17 (.leaf (-27)) (.branch 21 (.leaf (-26)) (.leaf (-25)))) (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-16)) (.leaf (-8))))),
  (.leaf (-18)),
  (.branch 28 (.branch 19 (.leaf (-21)) (.branch 27 (.leaf (-20)) (.leaf (-16)))) (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-8)) (.leaf (-4))))),
  (.branch 16 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 27 (.branch 15 (.leaf (-20)) (.branch 26 (.leaf (-18)) (.leaf (-15)))) (.branch 29 (.branch 28 (.leaf (-12)) (.leaf (-9))) (.branch 30 (.leaf (-6)) (.leaf (-3))))),
  (.branch 30 (.leaf (-4)) (.leaf (-3))),
  (.branch 26 (.branch 23 (.branch 22 (.leaf (-20)) (.leaf (-18))) (.branch 24 (.leaf (-16)) (.branch 25 (.leaf (-14)) (.leaf (-12))))) (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-8))) (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-4)) (.leaf (-2))))))]
def witnessD7_059_1075 : CycleWitness 7 where
  length := 31
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (4))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (6)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.leaf (3)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (5)) (.leaf (0))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (2)) (.leaf (4))) (.branch 26 (.leaf (0)) (.leaf (3)))) (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1075
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 18 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 26 (.leaf (9)) (.branch 29 (.leaf (10)) (.leaf (11)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 20 (.leaf (-20)) (.leaf (-28)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 17 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 6 (.leaf (0)) (.leaf (-19))),
  (.branch 14 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 24 (.branch 21 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.branch 30 (.leaf (-25)) (.leaf (-16))))),
  (.branch 22 (.branch 9 (.leaf (-14)) (.leaf (-13))) (.branch 29 (.leaf (-11)) (.branch 30 (.leaf (-8)) (.leaf (-5))))),
  (.branch 25 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-2)) (.leaf (0)))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.leaf (-2)))),
  (.branch 27 (.branch 10 (.leaf (-13)) (.branch 26 (.leaf (-12)) (.leaf (-10)))) (.branch 29 (.branch 28 (.leaf (-8)) (.leaf (-6))) (.branch 30 (.leaf (-4)) (.leaf (-2))))),
  (.branch 26 (.branch 23 (.branch 7 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-16)) (.branch 25 (.leaf (-14)) (.leaf (-12))))) (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-8))) (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 15 (.leaf (-3)) (.leaf (-2)))]
def witnessD7_059_1076 : CycleWitness 7 where
  length := 31
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (6))) (.branch 22 (.leaf (0)) (.leaf (2))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (4)) (.leaf (0))) (.branch 26 (.leaf (3)) (.leaf (1)))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1076
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 28 (.leaf (9)) (.branch 30 (.leaf (10)) (.leaf (11)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 14 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 20 (.leaf (-15)) (.leaf (-16)))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 23 (.leaf (-5)) (.branch 29 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-19)) (.leaf (-21)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-25))),
  (.branch 21 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 2 (.leaf (-17)) (.leaf (-16))),
  (.branch 28 (.branch 21 (.leaf (-16)) (.leaf (-14))) (.branch 29 (.leaf (-11)) (.branch 30 (.leaf (-8)) (.leaf (-5))))),
  (.branch 30 (.leaf (-7)) (.leaf (-5))),
  (.branch 28 (.branch 19 (.leaf (-21)) (.branch 27 (.leaf (-20)) (.leaf (-16)))) (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-8)) (.leaf (-4))))),
  (.branch 16 (.leaf (-1)) (.leaf (0))),
  (.branch 18 (.branch 12 (.branch 9 (.branch 7 (.leaf (-25)) (.branch 8 (.leaf (-24)) (.leaf (-23)))) (.branch 10 (.leaf (-22)) (.branch 11 (.leaf (-21)) (.leaf (-20))))) (.branch 15 (.branch 13 (.leaf (-19)) (.branch 14 (.leaf (-18)) (.leaf (-17)))) (.branch 16 (.leaf (-16)) (.branch 17 (.leaf (-15)) (.leaf (-14)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-13)) (.branch 20 (.leaf (-12)) (.leaf (-11)))) (.branch 22 (.leaf (-10)) (.branch 23 (.leaf (-9)) (.leaf (-8))))) (.branch 27 (.branch 25 (.leaf (-7)) (.branch 26 (.leaf (-6)) (.leaf (-5)))) (.branch 29 (.branch 28 (.leaf (-4)) (.leaf (-3))) (.branch 30 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-9))) (.branch 24 (.leaf (-8)) (.branch 25 (.leaf (-7)) (.leaf (-6))))) (.branch 28 (.branch 27 (.leaf (-5)) (.leaf (-4))) (.branch 29 (.leaf (-3)) (.branch 30 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_059_1077 : CycleWitness 7 where
  length := 31
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (4))) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (6))) (.branch 14 (.leaf (3)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 21 (.branch 20 (.leaf (5)) (.leaf (2))) (.branch 22 (.leaf (0)) (.leaf (3))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (1)) (.leaf (4))) (.branch 26 (.leaf (0)) (.leaf (2)))) (.branch 29 (.branch 28 (.leaf (6)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1077
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 18 (.leaf (-10)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-7)))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-15)) (.leaf (-17)))),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (-21)) (.leaf (-22)))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 23 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9)))),
  (.branch 25 (.branch 20 (.leaf (-7)) (.leaf (-6))) (.branch 30 (.leaf (-5)) (.leaf (-3)))),
  (.branch 22 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-15))) (.branch 26 (.leaf (-13)) (.leaf (-11)))) (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-7))) (.branch 30 (.leaf (-5)) (.leaf (-3))))),
  (.branch 27 (.branch 10 (.leaf (-13)) (.branch 26 (.leaf (-12)) (.leaf (-10)))) (.branch 29 (.branch 28 (.leaf (-8)) (.leaf (-6))) (.branch 30 (.leaf (-4)) (.leaf (-2))))),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-22)) (.leaf (-20))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-16)) (.leaf (-14))))) (.branch 28 (.branch 26 (.leaf (-12)) (.branch 27 (.leaf (-10)) (.leaf (-8)))) (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-4)) (.leaf (-2))))]
def witnessD7_059_1078 : CycleWitness 7 where
  length := 31
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (3)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (4)) (.leaf (0))) (.branch 18 (.leaf (3)) (.leaf (2)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (4)) (.leaf (2))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (5)) (.leaf (0))) (.branch 26 (.leaf (3)) (.leaf (1)))) (.branch 29 (.branch 28 (.leaf (6)) (.leaf (0))) (.branch 30 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1078
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-23))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 20 (.leaf (-18)) (.leaf (-20)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 23 (.leaf (-2)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-19)) (.leaf (-22)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (-19))) (.branch 24 (.leaf (-20)) (.leaf (-21)))),
  (.branch 11 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 14 (.branch 6 (.branch 2 (.leaf (-23)) (.leaf (-22))) (.branch 10 (.leaf (-21)) (.leaf (-20)))) (.branch 22 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 26 (.leaf (-17)) (.branch 30 (.leaf (-16)) (.leaf (-8)))))),
  (.branch 28 (.branch 21 (.leaf (-20)) (.leaf (-17))) (.branch 29 (.leaf (-13)) (.branch 30 (.leaf (-9)) (.leaf (-5))))),
  (.branch 24 (.leaf (-6)) (.leaf (-5))),
  (.branch 27 (.branch 11 (.leaf (-22)) (.branch 19 (.leaf (-21)) (.leaf (-20)))) (.branch 29 (.branch 28 (.leaf (-16)) (.leaf (-12))) (.branch 30 (.leaf (-8)) (.leaf (-4))))),
  (.branch 23 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 27 (.branch 25 (.leaf (-21)) (.branch 26 (.leaf (-18)) (.leaf (-15)))) (.branch 29 (.branch 28 (.leaf (-12)) (.leaf (-9))) (.branch 30 (.leaf (-6)) (.leaf (-3))))),
  (.branch 29 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.leaf (-2))))]
def witnessD7_059_1079 : CycleWitness 7 where
  length := 31
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (4))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (1)) (.leaf (3))) (.branch 18 (.leaf (0)) (.leaf (6)))) (.branch 21 (.branch 20 (.leaf (2)) (.leaf (1))) (.branch 22 (.leaf (4)) (.leaf (0))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (3)) (.leaf (2))) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 29 (.branch 28 (.leaf (4)) (.leaf (3))) (.branch 30 (.leaf (1)) (.leaf (2)))))))
  code := certificateD7_1079
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-24))) (.branch 9 (.leaf (-27)) (.leaf (-30)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 30 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 17 (.leaf (-3)) (.branch 29 (.leaf (-4)) (.leaf (-6))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (-2))) (.branch 28 (.leaf (-5)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-28))),
  (.branch 19 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 28 (.branch 10 (.leaf (-30)) (.branch 19 (.leaf (-29)) (.leaf (-28)))) (.branch 29 (.leaf (-21)) (.branch 30 (.leaf (-14)) (.leaf (-7))))),
  (.leaf (-5)),
  (.branch 5 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (0)))),
  (.branch 30 (.leaf (-6)) (.leaf (-5))),
  (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6)))),
  (.branch 17 (.branch 10 (.branch 6 (.branch 4 (.leaf (-28)) (.branch 5 (.leaf (-27)) (.leaf (-26)))) (.branch 8 (.branch 7 (.leaf (-25)) (.leaf (-24))) (.branch 9 (.leaf (-23)) (.leaf (-22))))) (.branch 13 (.branch 11 (.leaf (-21)) (.branch 12 (.leaf (-20)) (.leaf (-19)))) (.branch 15 (.branch 14 (.leaf (-18)) (.leaf (-17))) (.branch 16 (.leaf (-16)) (.leaf (-15)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (-14)) (.branch 19 (.leaf (-13)) (.leaf (-12)))) (.branch 22 (.branch 21 (.leaf (-11)) (.leaf (-10))) (.branch 23 (.leaf (-9)) (.leaf (-8))))) (.branch 27 (.branch 25 (.leaf (-7)) (.branch 26 (.leaf (-6)) (.leaf (-5)))) (.branch 29 (.branch 28 (.leaf (-4)) (.leaf (-3))) (.branch 30 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 22 (.branch 20 (.leaf (-12)) (.branch 21 (.leaf (-11)) (.leaf (-10)))) (.branch 23 (.leaf (-9)) (.branch 24 (.leaf (-8)) (.leaf (-7))))) (.branch 28 (.branch 26 (.leaf (-6)) (.branch 27 (.leaf (-5)) (.leaf (-4)))) (.branch 29 (.leaf (-3)) (.branch 30 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_059_1080 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 23 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (5)) (.leaf (0))) (.branch 27 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1080
  counts := ![(.branch 14 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (5)) (.leaf (6))) (.branch 11 (.leaf (7)) (.branch 13 (.leaf (8)) (.leaf (9)))))) (.branch 22 (.branch 17 (.branch 16 (.leaf (10)) (.leaf (11))) (.branch 19 (.leaf (12)) (.branch 20 (.leaf (13)) (.leaf (14))))) (.branch 26 (.branch 23 (.leaf (15)) (.branch 25 (.leaf (16)) (.leaf (17)))) (.branch 28 (.leaf (18)) (.branch 29 (.leaf (19)) (.leaf (20))))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-24))),
  (.branch 12 (.leaf (0)) (.leaf (-18))),
  (.branch 18 (.leaf (0)) (.leaf (-12))),
  (.branch 24 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.leaf (-2)),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 12 (.branch 9 (.branch 7 (.leaf (-24)) (.branch 8 (.leaf (-23)) (.leaf (-22)))) (.branch 10 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19))))) (.branch 15 (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 16 (.branch 14 (.branch 13 (.leaf (-18)) (.leaf (-17))) (.branch 15 (.leaf (-16)) (.leaf (-15)))) (.branch 18 (.branch 17 (.leaf (-14)) (.leaf (-13))) (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_059_1081 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))) (.branch 12 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 23 (.leaf (5)) (.branch 24 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (6)) (.leaf (1)))))))
  code := certificateD7_1081
  counts := ![(.branch 14 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 22 (.branch 19 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 20 (.leaf (10)) (.leaf (11)))) (.branch 26 (.branch 25 (.leaf (12)) (.leaf (13))) (.branch 28 (.leaf (14)) (.leaf (15)))))),
  (.branch 15 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-25))),
  (.branch 11 (.leaf (0)) (.leaf (-19))),
  (.branch 17 (.leaf (0)) (.leaf (-13))),
  (.branch 23 (.leaf (0)) (.leaf (-7))),
  (.branch 29 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 17 (.branch 11 (.branch 8 (.branch 6 (.leaf (-25)) (.branch 7 (.leaf (-24)) (.leaf (-23)))) (.branch 9 (.leaf (-22)) (.branch 10 (.leaf (-21)) (.leaf (-20))))) (.branch 14 (.branch 12 (.leaf (-19)) (.branch 13 (.leaf (-18)) (.leaf (-17)))) (.branch 15 (.leaf (-16)) (.branch 16 (.leaf (-15)) (.leaf (-14)))))) (.branch 23 (.branch 20 (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 20 (.branch 15 (.branch 13 (.branch 12 (.leaf (-19)) (.leaf (-18))) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 20 (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_059_1082 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (5)) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (4)) (.leaf (0))) (.branch 22 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (6)) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (1)))))))
  code := certificateD7_1082
  counts := ![(.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.branch 29 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-25))),
  (.branch 20 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.leaf (0)) (.leaf (-21))),
  (.branch 24 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 22 (.branch 18 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))) (.branch 26 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))),
  (.branch 23 (.branch 19 (.leaf (-3)) (.leaf (-2))) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.branch 11 (.branch 8 (.branch 6 (.leaf (-25)) (.branch 7 (.leaf (-24)) (.leaf (-23)))) (.branch 9 (.leaf (-22)) (.branch 10 (.leaf (-21)) (.leaf (-20))))) (.branch 14 (.branch 12 (.leaf (-19)) (.branch 13 (.leaf (-18)) (.leaf (-17)))) (.branch 15 (.leaf (-16)) (.branch 16 (.leaf (-15)) (.leaf (-14)))))) (.branch 23 (.branch 20 (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-21)) (.leaf (-20))) (.branch 12 (.leaf (-19)) (.branch 13 (.leaf (-18)) (.leaf (-17))))) (.branch 16 (.branch 15 (.leaf (-16)) (.leaf (-15))) (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_059_1083 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (5)) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (3)) (.leaf (0))) (.branch 22 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (6)) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1083
  counts := ![(.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.branch 29 (.leaf (15)) (.leaf (16))))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-21))),
  (.branch 24 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 22 (.branch 18 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))) (.branch 26 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))),
  (.branch 27 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-21)) (.leaf (-20))) (.branch 12 (.leaf (-19)) (.branch 13 (.leaf (-18)) (.leaf (-17))))) (.branch 16 (.branch 15 (.leaf (-16)) (.leaf (-15))) (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_059_1084 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1084
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 17 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 19 (.leaf (9)) (.leaf (10)))) (.branch 26 (.branch 24 (.leaf (11)) (.leaf (12))) (.branch 28 (.leaf (13)) (.leaf (14)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))) (.branch 17 (.leaf (-13)) (.branch 19 (.leaf (-14)) (.leaf (-15))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-18))),
  (.branch 27 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 20 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-9)))),
  (.branch 27 (.branch 26 (.leaf (-10)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.branch 16 (.branch 14 (.branch 13 (.leaf (-18)) (.leaf (-17))) (.branch 15 (.leaf (-16)) (.leaf (-15)))) (.branch 18 (.branch 17 (.leaf (-14)) (.leaf (-13))) (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_059_1085 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (5)) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (4)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (6)) (.branch 22 (.leaf (0)) (.leaf (3))))) (.branch 27 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1085
  counts := ![(.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))))) (.branch 22 (.branch 17 (.branch 16 (.leaf (9)) (.leaf (10))) (.branch 19 (.leaf (11)) (.branch 21 (.leaf (12)) (.leaf (13))))) (.branch 26 (.branch 24 (.leaf (14)) (.leaf (15))) (.branch 27 (.leaf (16)) (.branch 29 (.leaf (17)) (.leaf (18))))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-25))),
  (.branch 20 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 28 (.leaf (-4)) (.leaf (-3))),
  (.branch 27 (.branch 26 (.leaf (-10)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 17 (.branch 11 (.branch 8 (.branch 6 (.leaf (-25)) (.branch 7 (.leaf (-24)) (.leaf (-23)))) (.branch 9 (.leaf (-22)) (.branch 10 (.leaf (-21)) (.leaf (-20))))) (.branch 14 (.branch 12 (.leaf (-19)) (.branch 13 (.leaf (-18)) (.leaf (-17)))) (.branch 15 (.leaf (-16)) (.branch 16 (.leaf (-15)) (.leaf (-14)))))) (.branch 23 (.branch 20 (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_059_1086 : CycleWitness 7 where
  length := 30
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (6)) (.leaf (1))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (5)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (2)) (.leaf (6))))) (.branch 26 (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1086
  counts := ![(.branch 13 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 14 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 14 (.leaf (-14)) (.branch 27 (.leaf (-18)) (.leaf (-19))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 24 (.leaf (-10)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-10)) (.leaf (-11)))),
  (.branch 7 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 28 (.leaf (-19)) (.branch 29 (.leaf (-16)) (.leaf (-13)))),
  (.branch 25 (.leaf (-12)) (.leaf (-9))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 24 (.branch 8 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_059_1087 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (5))) (.branch 14 (.leaf (1)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (3)))) (.branch 21 (.branch 20 (.leaf (4)) (.leaf (0))) (.branch 22 (.leaf (1)) (.leaf (2))))) (.branch 26 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (1)) (.leaf (2)))))))
  code := certificateD7_1087
  counts := ![(.branch 12 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 17 (.leaf (-18)) (.leaf (-23)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 25 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.leaf (-17))),
  (.branch 28 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 28 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 29 (.leaf (-18)) (.leaf (-14)))),
  (.leaf (-4)),
  (.leaf (0)),
  (.branch 27 (.branch 26 (.leaf (-7)) (.leaf (-6))) (.branch 28 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-3))))),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.branch 17 (.branch 15 (.branch 14 (.leaf (-17)) (.leaf (-16))) (.branch 16 (.leaf (-15)) (.leaf (-14)))) (.branch 19 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-11)) (.leaf (-10))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_059_1088 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (5))) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (4)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (0)) (.leaf (1)))))))
  code := certificateD7_1088
  counts := ![(.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.branch 29 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 22 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-17))),
  (.branch 28 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 22 (.branch 18 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))) (.branch 26 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))),
  (.branch 25 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-23)) (.leaf (-22))) (.branch 10 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19))))) (.branch 15 (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 17 (.branch 15 (.branch 14 (.leaf (-17)) (.leaf (-16))) (.branch 16 (.leaf (-15)) (.leaf (-14)))) (.branch 19 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-11)) (.leaf (-10))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_059_1089 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (4))) (.branch 22 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (6)) (.leaf (1)))))))
  code := certificateD7_1089
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 17 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 19 (.leaf (9)) (.leaf (10)))) (.branch 26 (.branch 24 (.leaf (11)) (.leaf (12))) (.branch 28 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))) (.branch 17 (.leaf (-13)) (.branch 19 (.leaf (-14)) (.leaf (-15))))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-16))),
  (.branch 29 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 20 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 26 (.branch 24 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 18 (.branch 16 (.branch 15 (.leaf (-16)) (.leaf (-15))) (.branch 17 (.leaf (-14)) (.leaf (-13)))) (.branch 20 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.leaf (-9))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_059_1090 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (5))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (6))) (.branch 22 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (1)))))))
  code := certificateD7_1090
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 17 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 19 (.leaf (9)) (.leaf (10)))) (.branch 26 (.branch 24 (.leaf (11)) (.leaf (12))) (.branch 28 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))) (.branch 17 (.leaf (-13)) (.branch 19 (.leaf (-14)) (.leaf (-15))))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 14 (.leaf (0)) (.leaf (-16))),
  (.branch 29 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-24))),
  (.branch 21 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 20 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 18 (.branch 16 (.branch 15 (.leaf (-16)) (.leaf (-15))) (.branch 17 (.leaf (-14)) (.leaf (-13)))) (.branch 20 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.leaf (-9))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 18 (.branch 12 (.branch 9 (.branch 7 (.leaf (-24)) (.branch 8 (.leaf (-23)) (.leaf (-22)))) (.branch 10 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19))))) (.branch 15 (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_059_1091 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (5))) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (0)) (.leaf (1)))))))
  code := certificateD7_1091
  counts := ![(.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.branch 29 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.leaf (0)) (.leaf (-17))),
  (.branch 28 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 22 (.branch 18 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))) (.branch 26 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))),
  (.branch 25 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 17 (.branch 15 (.branch 14 (.leaf (-17)) (.leaf (-16))) (.branch 16 (.leaf (-15)) (.leaf (-14)))) (.branch 19 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-11)) (.leaf (-10))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_059_1092 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (3)) (.leaf (0))) (.branch 22 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (6)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1092
  counts := ![(.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 25 (.branch 23 (.leaf (12)) (.leaf (13))) (.branch 27 (.leaf (14)) (.branch 29 (.leaf (15)) (.leaf (16))))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 28 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-19))),
  (.branch 26 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 22 (.branch 18 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))) (.branch 26 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))),
  (.branch 29 (.leaf (-4)) (.leaf (-3))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 15 (.branch 13 (.branch 12 (.leaf (-19)) (.leaf (-18))) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_059_1093 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (1)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (1)))))))
  code := certificateD7_1093
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 25 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 6 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 19 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 17 (.leaf (-16)) (.leaf (-19)))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-27))),
  (.branch 18 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 26 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 29 (.leaf (-16)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 16 (.branch 9 (.branch 6 (.branch 4 (.leaf (-27)) (.branch 5 (.leaf (-26)) (.leaf (-25)))) (.branch 7 (.leaf (-24)) (.branch 8 (.leaf (-23)) (.leaf (-22))))) (.branch 12 (.branch 10 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19)))) (.branch 14 (.branch 13 (.leaf (-18)) (.leaf (-17))) (.branch 15 (.leaf (-16)) (.leaf (-15)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))) (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_059_1094 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (5))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1094
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 26 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-21))),
  (.branch 24 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 21 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 18 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 28 (.branch 20 (.leaf (-7)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-21)) (.leaf (-20))) (.branch 12 (.leaf (-19)) (.branch 13 (.leaf (-18)) (.leaf (-17))))) (.branch 16 (.branch 15 (.leaf (-16)) (.leaf (-15))) (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_059 : Fin 32 → CycleWitness 7 := ![witnessD7_059_1063, witnessD7_059_1064, witnessD7_059_1065, witnessD7_059_1066, witnessD7_059_1067, witnessD7_059_1068, witnessD7_059_1069, witnessD7_059_1070, witnessD7_059_1071, witnessD7_059_1072, witnessD7_059_1073, witnessD7_059_1074, witnessD7_059_1075, witnessD7_059_1076, witnessD7_059_1077, witnessD7_059_1078, witnessD7_059_1079, witnessD7_059_1080, witnessD7_059_1081, witnessD7_059_1082, witnessD7_059_1083, witnessD7_059_1084, witnessD7_059_1085, witnessD7_059_1086, witnessD7_059_1087, witnessD7_059_1088, witnessD7_059_1089, witnessD7_059_1090, witnessD7_059_1091, witnessD7_059_1092, witnessD7_059_1093, witnessD7_059_1094]
end RealPinwheel.FiveSixths


