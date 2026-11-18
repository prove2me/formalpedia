-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_010
-- name    : RealPinwheel_FiveSixths_WitnessD6_010
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:36:35.405315+00:00
-- url     : https://prove2.me/theorems/f15a1c67-0f8d-46c3-9f2d-5622fa2f20b8
-- title:
--   Exact witness block D6_010
-- statement:
--   These exact witnesses represent words 256 through 290 of source certificate file D6. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D6, entries 256–290; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D6.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD6
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD6_010_255 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 5 (.leaf (4)) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (5))) (.branch 13 (.leaf (1)) (.leaf (3)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1)))) (.branch 19 (.leaf (4)) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (5))) (.branch 27 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_255
  counts := ![(.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 16 (.leaf (-6)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 14 (.leaf (-3)) (.branch 25 (.leaf (-4)) (.leaf (-5))))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))),
  (.branch 4 (.leaf (-5)) (.branch 23 (.leaf (-4)) (.leaf (-3)))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3)))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_010_256 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (1)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (4)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (5)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (1)))))))
  code := certificateD6_256
  counts := ![(.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-17)) (.leaf (-34)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.leaf (-5)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (-1))) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-14)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-6))))]
  high := ![(.branch 15 (.branch 6 (.branch 3 (.leaf (-34)) (.leaf (-33))) (.branch 9 (.leaf (-32)) (.branch 12 (.leaf (-31)) (.leaf (-30))))) (.branch 21 (.branch 18 (.leaf (-29)) (.leaf (-28))) (.branch 24 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-17)))))),
  (.branch 16 (.leaf (-5)) (.branch 26 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-3)),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 19 (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))) (.branch 20 (.leaf (-11)) (.branch 21 (.leaf (-10)) (.leaf (-9))))) (.branch 25 (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 26 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.leaf (-3))))]
def witnessD6_010_257 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (1)))))))
  code := certificateD6_257
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (7)) (.leaf (8))) (.branch 18 (.leaf (9)) (.leaf (10)))) (.branch 24 (.branch 22 (.leaf (11)) (.leaf (12))) (.branch 26 (.leaf (13)) (.leaf (14)))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-15))),
  (.branch 27 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.branch 16 (.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_010_258 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 5 (.leaf (4)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (5)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (1)))))))
  code := certificateD6_258
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (7)) (.leaf (8))) (.branch 18 (.leaf (9)) (.leaf (10)))) (.branch 25 (.branch 23 (.leaf (11)) (.leaf (12))) (.branch 27 (.leaf (13)) (.leaf (14)))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-19)) (.leaf (-20)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (-4))) (.branch 26 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 21 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 24 (.branch 13 (.leaf (-20)) (.branch 23 (.leaf (-18)) (.leaf (-15)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 27 (.leaf (-6)) (.leaf (-3))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_010_259 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (1)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (4)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (5)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_259
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 23 (.leaf (9)) (.branch 26 (.leaf (10)) (.leaf (11)))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.branch 19 (.leaf (-11)) (.leaf (-16)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 24 (.branch 3 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-13)) (.leaf (-8)))),
  (.branch 13 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-9))))),
  (.branch 26 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-11)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_010_260 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (4)))))))
  code := certificateD6_260
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 25 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.leaf (12)))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-1))) (.branch 6 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 21 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 27 (.leaf (-6)) (.leaf (-3))),
  (.leaf (-3)),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 10 (.leaf (-19)) (.branch 11 (.leaf (-18)) (.leaf (-17))))) (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 21 (.branch 17 (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))) (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.leaf (-8))))) (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_010_261 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (5))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_261
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (11)) (.leaf (12)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 21 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 27 (.leaf (-6)) (.leaf (-3))),
  (.branch 26 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-3)),
  (.leaf (0)),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 10 (.leaf (-19)) (.branch 11 (.leaf (-18)) (.leaf (-17))))) (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_010_262 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (3)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (1)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_262
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 11 (.leaf (-3)) (.branch 25 (.leaf (-5)) (.leaf (-7))))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-2)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 21 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 21 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))),
  (.branch 23 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 10 (.leaf (-19)) (.branch 11 (.leaf (-18)) (.leaf (-17))))) (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_010_263 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (5)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (3)) (.branch 19 (.leaf (1)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (4)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (5)))))))
  code := certificateD6_263
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 11 (.leaf (-3)) (.branch 25 (.leaf (-5)) (.leaf (-7))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-16))) (.branch 22 (.leaf (-17)) (.leaf (-18)))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 21 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))),
  (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-15)) (.leaf (-12)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 9 (.leaf (-4)) (.leaf (-3))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_010_264 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (5)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_264
  counts := ![(.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.leaf (12)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-19))),
  (.branch 23 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 25 (.leaf (-5)) (.leaf (-3))),
  (.branch 26 (.branch 20 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 19 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 13 (.branch 11 (.branch 10 (.leaf (-19)) (.leaf (-18))) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 15 (.branch 14 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-13)) (.branch 17 (.leaf (-12)) (.leaf (-11)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_010_265 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (5))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (2)))))))
  code := certificateD6_265
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 20 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-16)) (.leaf (-17)))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 4 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-11)))),
  (.branch 26 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 25 (.branch 14 (.leaf (-17)) (.branch 24 (.leaf (-15)) (.leaf (-12)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_010_266 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_266
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-4)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-24))),
  (.branch 18 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 21 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 25 (.leaf (-6)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 10 (.branch 7 (.branch 5 (.leaf (-24)) (.branch 6 (.leaf (-23)) (.leaf (-22)))) (.branch 8 (.leaf (-21)) (.branch 9 (.leaf (-20)) (.leaf (-19))))) (.branch 13 (.branch 11 (.leaf (-18)) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))))) (.branch 22 (.branch 19 (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_010_267 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_267
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-18))) (.branch 24 (.leaf (-19)) (.leaf (-20)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-3)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 21 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.branch 25 (.leaf (-20)) (.leaf (-15))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.branch 11 (.leaf (-6)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_010_268 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_268
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 20 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.leaf (-6))),
  (.branch 14 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 19 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5))))),
  (.branch 27 (.leaf (-4)) (.leaf (-2))),
  (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3)))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 17 (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))) (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.leaf (-8))))) (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_010_269 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (4)))))))
  code := certificateD6_269
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 27 (.leaf (-10)) (.leaf (-5))),
  (.branch 20 (.leaf (-4)) (.branch 24 (.leaf (-3)) (.leaf (-2)))),
  (.branch 26 (.branch 9 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.branch 24 (.branch 7 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7)))) (.branch 26 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-17)) (.leaf (-16))) (.branch 14 (.leaf (-15)) (.leaf (-14)))) (.branch 17 (.branch 16 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-11)) (.leaf (-10))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD6_010_270 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (5)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_270
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-20))),
  (.branch 22 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 19 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5))))),
  (.branch 27 (.leaf (-4)) (.leaf (-2))),
  (.branch 26 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.leaf (-1)) (.leaf (0))),
  (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-20)) (.leaf (-19))) (.branch 11 (.leaf (-18)) (.branch 12 (.leaf (-17)) (.leaf (-16))))) (.branch 15 (.branch 14 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-13)) (.branch 17 (.leaf (-12)) (.leaf (-11)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_010_271 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (4)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (5)) (.leaf (2)))))))
  code := certificateD6_271
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-15))),
  (.branch 27 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 26 (.leaf (-6)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 27 (.leaf (-4)) (.leaf (-2))),
  (.branch 25 (.leaf (-1)) (.leaf (0))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.branch 16 (.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_010_272 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (3)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (5)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (2)))))))
  code := certificateD6_272
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-18))),
  (.branch 24 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 23 (.branch 19 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 19 (.branch 14 (.branch 12 (.branch 11 (.leaf (-18)) (.leaf (-17))) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 16 (.branch 15 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_010_273 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (5)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (4))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (5)) (.leaf (3)))))))
  code := certificateD6_273
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 26 (.leaf (-6)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.leaf (-3)))),
  (.branch 21 (.branch 15 (.leaf (-14)) (.leaf (-12))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD6_010_274 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (5)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_274
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-19))),
  (.branch 23 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 19 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5))))),
  (.branch 26 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.branch 23 (.leaf (-3)) (.leaf (-2))) (.branch 25 (.leaf (-1)) (.leaf (0)))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 13 (.branch 11 (.branch 10 (.leaf (-19)) (.leaf (-18))) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 15 (.branch 14 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-13)) (.branch 17 (.leaf (-12)) (.leaf (-11)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_010_275 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (5))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (1)))))))
  code := certificateD6_275
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 21 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 16 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 21 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-5)) (.branch 26 (.leaf (-2)) (.leaf (0))))),
  (.branch 18 (.leaf (-5)) (.branch 23 (.leaf (-4)) (.leaf (-3)))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 10 (.leaf (-19)) (.branch 11 (.leaf (-18)) (.leaf (-17))))) (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_010_276 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (5))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (4)))))))
  code := certificateD6_276
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 23 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 17 (.leaf (-3)) (.leaf (-2))),
  (.branch 26 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 5 (.leaf (-16)) (.branch 24 (.leaf (-15)) (.leaf (-12)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 19 (.leaf (-2)) (.leaf (0))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_010_277 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (5)))))))
  code := certificateD6_277
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 23 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 25 (.branch 5 (.leaf (-16)) (.branch 24 (.leaf (-15)) (.leaf (-12)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 19 (.leaf (-2)) (.leaf (0)))]
def witnessD6_010_278 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (3))) (.branch 13 (.leaf (1)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (5)) (.branch 23 (.leaf (3)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (2))) (.branch 27 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_278
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-11)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 25 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.leaf (-4)) (.leaf (-3))),
  (.branch 21 (.branch 15 (.leaf (-14)) (.leaf (-12))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_010_279 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (4))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (5)) (.leaf (2)))))))
  code := certificateD6_279
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD6_010_280 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (4)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (5)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (3)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (4)) (.leaf (2)))))))
  code := certificateD6_280
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-18))) (.branch 11 (.leaf (-22)) (.branch 21 (.leaf (-23)) (.leaf (-28))))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 26 (.branch 22 (.leaf (-28)) (.leaf (-25))) (.branch 27 (.leaf (-18)) (.leaf (-11)))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_010_281 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (1)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (2)) (.leaf (5)))))))
  code := certificateD6_281
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-18)) (.leaf (-21)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 21 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0))]
  high := ![(.branch 26 (.leaf (-6)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 22 (.leaf (-7)) (.leaf (-5))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0))]
def witnessD6_010_282 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_282
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-25))),
  (.branch 17 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 23 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 25 (.leaf (-1)) (.leaf (0))),
  (.branch 15 (.branch 9 (.branch 6 (.branch 4 (.leaf (-25)) (.branch 5 (.leaf (-24)) (.leaf (-23)))) (.branch 7 (.leaf (-22)) (.branch 8 (.leaf (-21)) (.leaf (-20))))) (.branch 12 (.branch 10 (.leaf (-19)) (.branch 11 (.leaf (-18)) (.leaf (-17)))) (.branch 13 (.leaf (-16)) (.branch 14 (.leaf (-15)) (.leaf (-14)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (-13)) (.branch 17 (.leaf (-12)) (.leaf (-11)))) (.branch 19 (.leaf (-10)) (.branch 20 (.leaf (-9)) (.leaf (-8))))) (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_010_283 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (1)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (4)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_283
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-18))) (.branch 24 (.leaf (-19)) (.leaf (-20)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-3)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 21 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.branch 25 (.leaf (-20)) (.leaf (-15))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.branch 11 (.leaf (-6)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_010_284 : CycleWitness 6 where
  length := 27
  word := (.branch 14 (.branch 8 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_284
  counts := ![(.branch 13 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (9)) (.leaf (10))) (.branch 18 (.leaf (11)) (.leaf (12)))) (.branch 23 (.branch 21 (.leaf (13)) (.leaf (14))) (.branch 24 (.leaf (15)) (.branch 26 (.leaf (16)) (.leaf (17))))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 8 (.leaf (-7)) (.branch 11 (.leaf (-8)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-6)) (.leaf (-7)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.branch 25 (.leaf (-1)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-21))),
  (.branch 22 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 20 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-6)))),
  (.branch 23 (.branch 21 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.leaf (-5)) (.leaf (-4))),
  (.branch 16 (.branch 11 (.branch 8 (.branch 7 (.leaf (-21)) (.leaf (-20))) (.branch 9 (.leaf (-19)) (.branch 10 (.leaf (-18)) (.leaf (-17))))) (.branch 13 (.branch 12 (.leaf (-16)) (.leaf (-15))) (.branch 14 (.leaf (-14)) (.branch 15 (.leaf (-13)) (.leaf (-12)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-11)) (.leaf (-10))) (.branch 19 (.leaf (-9)) (.branch 20 (.leaf (-8)) (.leaf (-7))))) (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_010_285 : CycleWitness 6 where
  length := 27
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (0)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (1)))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (1)))))))
  code := certificateD6_285
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (7)) (.leaf (8))) (.branch 18 (.leaf (9)) (.leaf (10)))) (.branch 24 (.branch 22 (.leaf (11)) (.leaf (12))) (.branch 26 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 5 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-13)) (.leaf (-26)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 25 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-14))),
  (.branch 19 (.leaf (0)) (.leaf (-8))),
  (.branch 7 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 13 (.branch 7 (.branch 3 (.leaf (-26)) (.branch 5 (.leaf (-25)) (.leaf (-24)))) (.branch 9 (.leaf (-23)) (.branch 11 (.leaf (-22)) (.leaf (-21))))) (.branch 19 (.branch 15 (.leaf (-20)) (.branch 17 (.leaf (-19)) (.leaf (-18)))) (.branch 23 (.branch 21 (.leaf (-17)) (.leaf (-16))) (.branch 25 (.leaf (-15)) (.leaf (-14)))))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.branch 16 (.branch 14 (.leaf (-14)) (.branch 15 (.leaf (-13)) (.leaf (-12)))) (.branch 18 (.branch 17 (.leaf (-11)) (.leaf (-10))) (.branch 19 (.leaf (-9)) (.leaf (-8))))) (.branch 23 (.branch 21 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-8)) (.leaf (-7))) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-20)) (.leaf (-19))) (.branch 10 (.leaf (-18)) (.branch 11 (.leaf (-17)) (.leaf (-16))))) (.branch 14 (.branch 13 (.leaf (-15)) (.leaf (-14))) (.branch 15 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-11)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-10)) (.leaf (-9))) (.branch 20 (.leaf (-8)) (.branch 21 (.leaf (-7)) (.leaf (-6))))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD6_010_286 : CycleWitness 6 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (5)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (4))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (5)) (.leaf (3)))))))
  code := certificateD6_286
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 25 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-10)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 24 (.leaf (-11)) (.leaf (-18)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 15 (.leaf (-10)) (.leaf (-15)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 20 (.branch 17 (.leaf (-13)) (.leaf (-12))) (.branch 23 (.leaf (-11)) (.branch 26 (.leaf (-10)) (.leaf (-6))))),
  (.branch 25 (.leaf (-18)) (.branch 26 (.leaf (-14)) (.leaf (-10)))),
  (.branch 24 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-10)) (.leaf (-8))))),
  (.leaf (0)),
  (.branch 23 (.branch 21 (.branch 7 (.leaf (-15)) (.leaf (-14))) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2))]
def witnessD6_010_287 : CycleWitness 6 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (1)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (5)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (4)))))))
  code := certificateD6_287
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 16 (.leaf (-8)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 18 (.branch 4 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))),
  (.branch 20 (.branch 3 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-3)))),
  (.branch 25 (.branch 17 (.leaf (-13)) (.leaf (-12))) (.branch 26 (.leaf (-10)) (.leaf (-8)))),
  (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 23 (.branch 8 (.leaf (-13)) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))))]
def witnessD6_010_288 : CycleWitness 6 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (4)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_288
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 23 (.branch 21 (.leaf (9)) (.leaf (10))) (.branch 25 (.leaf (11)) (.leaf (12)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.branch 7 (.leaf (-7)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-19)) (.leaf (-22)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-19)) (.leaf (-20)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 26 (.leaf (-8)) (.leaf (-4))),
  (.branch 23 (.branch 9 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 25 (.branch 24 (.leaf (-16)) (.leaf (-12))) (.branch 26 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-4)),
  (.leaf (0)),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-20)) (.leaf (-18))) (.branch 20 (.leaf (-16)) (.branch 21 (.leaf (-14)) (.leaf (-12))))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2))))]
def witnessD6_010_289 : CycleWitness 6 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (3)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (5)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_289
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-20)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.leaf (0))]
  high := ![(.branch 25 (.branch 21 (.leaf (-22)) (.leaf (-21))) (.branch 26 (.leaf (-14)) (.leaf (-7)))),
  (.leaf (-2)),
  (.branch 12 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-8)))),
  (.branch 24 (.branch 13 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-16)) (.leaf (-14))) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD6_010 : Fin 35 → CycleWitness 6 := ![witnessD6_010_255, witnessD6_010_256, witnessD6_010_257, witnessD6_010_258, witnessD6_010_259, witnessD6_010_260, witnessD6_010_261, witnessD6_010_262, witnessD6_010_263, witnessD6_010_264, witnessD6_010_265, witnessD6_010_266, witnessD6_010_267, witnessD6_010_268, witnessD6_010_269, witnessD6_010_270, witnessD6_010_271, witnessD6_010_272, witnessD6_010_273, witnessD6_010_274, witnessD6_010_275, witnessD6_010_276, witnessD6_010_277, witnessD6_010_278, witnessD6_010_279, witnessD6_010_280, witnessD6_010_281, witnessD6_010_282, witnessD6_010_283, witnessD6_010_284, witnessD6_010_285, witnessD6_010_286, witnessD6_010_287, witnessD6_010_288, witnessD6_010_289]
end RealPinwheel.FiveSixths


