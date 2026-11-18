-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_009
-- name    : RealPinwheel_FiveSixths_WitnessD6_009
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:36:26.605139+00:00
-- url     : https://prove2.me/theorems/056d3662-dab5-478c-8dae-e267f2312bd8
-- title:
--   Exact witness block D6_009
-- statement:
--   These exact witnesses represent words 223 through 255 of source certificate file D6. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D6, entries 223–255; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D6.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD6
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD6_009_222 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (4))) (.branch 22 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (5)) (.leaf (1)))))))
  code := certificateD6_222
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 17 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 19 (.leaf (9)) (.leaf (10)))) (.branch 26 (.branch 24 (.leaf (11)) (.leaf (12))) (.branch 28 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))) (.branch 17 (.leaf (-13)) (.branch 19 (.leaf (-14)) (.leaf (-15))))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 20 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 26 (.branch 24 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_009_223 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (5)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (1)))))))
  code := certificateD6_223
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 25 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 6 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 19 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 17 (.leaf (-16)) (.leaf (-19)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-19))),
  (.branch 26 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 26 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 29 (.leaf (-16)) (.leaf (-11)))),
  (.leaf (0)),
  (.leaf (-2)),
  (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 15 (.branch 13 (.branch 12 (.leaf (-19)) (.leaf (-18))) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_009_224 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (2)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (5)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (2)))))))
  code := certificateD6_224
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 25 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 17 (.leaf (-16)) (.leaf (-19)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 26 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 29 (.leaf (-16)) (.leaf (-11)))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.leaf (-2)),
  (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_009_225 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (5))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_225
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 26 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 12 (.leaf (-3)) (.branch 27 (.leaf (-6)) (.leaf (-9))))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 22 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 21 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 18 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-23)) (.leaf (-22))) (.branch 10 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19))))) (.branch 15 (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_009_226 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (3))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_226
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 26 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-10)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (-2))) (.branch 27 (.leaf (-3)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 21 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 18 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 26 (.branch 13 (.leaf (-10)) (.branch 25 (.leaf (-9)) (.leaf (-8)))) (.branch 28 (.branch 27 (.leaf (-7)) (.leaf (-6))) (.branch 29 (.leaf (-5)) (.leaf (-4))))),
  (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-5)) (.leaf (-4)))),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_009_227 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (4)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_227
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 20 (.leaf (9)) (.leaf (10)))) (.branch 27 (.branch 24 (.leaf (11)) (.leaf (12))) (.branch 29 (.leaf (13)) (.leaf (14)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-8)) (.leaf (-9)))) (.branch 7 (.leaf (-10)) (.branch 9 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 10 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 25 (.leaf (-12)) (.leaf (-7))),
  (.branch 18 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.branch 22 (.leaf (-3)) (.leaf (-2))) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 20 (.branch 15 (.branch 12 (.branch 11 (.leaf (-20)) (.leaf (-19))) (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16))))) (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_009_228 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (4)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (4)))))))
  code := certificateD6_228
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (7)) (.leaf (8))) (.branch 20 (.leaf (9)) (.leaf (10)))) (.branch 27 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 29 (.leaf (13)) (.leaf (14)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 5 (.leaf (-9)) (.branch 7 (.leaf (-10)) (.leaf (-11))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 23 (.leaf (-11)) (.leaf (-7))),
  (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-10)) (.leaf (-8)))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 20 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-3)))),
  (.branch 27 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_009_229 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (0)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (5)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (2)))))))
  code := certificateD6_229
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 25 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-19))),
  (.branch 26 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 26 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.leaf (-1)) (.leaf (0))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.branch 20 (.branch 15 (.branch 13 (.branch 12 (.leaf (-19)) (.leaf (-18))) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_009_230 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (4))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_230
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 26 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-21))),
  (.branch 24 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 21 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 18 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 28 (.branch 20 (.leaf (-7)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-21)) (.leaf (-20))) (.branch 12 (.leaf (-19)) (.branch 13 (.leaf (-18)) (.leaf (-17))))) (.branch 16 (.branch 15 (.leaf (-16)) (.leaf (-15))) (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_009_231 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (4)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_231
  counts := ![(.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 26 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 29 (.leaf (-4)) (.leaf (-2))),
  (.branch 26 (.leaf (-5)) (.leaf (-3))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 21 (.branch 5 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.leaf (-1)) (.leaf (0)))]
def witnessD6_009_232 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (3)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (5)) (.leaf (2)))))))
  code := certificateD6_232
  counts := ![(.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 20 (.leaf (-12)) (.leaf (-15)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.branch 21 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-10)) (.leaf (-8))))),
  (.leaf (0)),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD6_009_233 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (5)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (4)))))))
  code := certificateD6_233
  counts := ![(.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 16 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 28 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 25 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 28 (.branch 20 (.leaf (-7)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_009_234 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (1)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (2))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (5)))))))
  code := certificateD6_234
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 16 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 23 (.leaf (-6)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.leaf (-8)) (.leaf (-4))),
  (.branch 24 (.leaf (-9)) (.leaf (-8))),
  (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 18 (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))) (.branch 20 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.leaf (-9))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_009_235 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (5)))))))
  code := certificateD6_235
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 11 (.leaf (-27)) (.leaf (-29)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-4)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-11)) (.leaf (-15)))),
  (.leaf (0))]
  high := ![(.branch 23 (.branch 12 (.leaf (-29)) (.leaf (-28))) (.branch 26 (.leaf (-25)) (.branch 29 (.leaf (-22)) (.leaf (-11))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))),
  (.branch 28 (.branch 27 (.leaf (-6)) (.leaf (-5))) (.branch 29 (.leaf (-4)) (.leaf (-3)))),
  (.branch 27 (.branch 25 (.leaf (-15)) (.branch 26 (.leaf (-13)) (.leaf (-11)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-7)) (.leaf (-5))))),
  (.leaf (0))]
def witnessD6_009_236 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (4))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (5))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (1)))))))
  code := certificateD6_236
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 28 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 30 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-21))),
  (.branch 24 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-21)) (.leaf (-20))) (.branch 12 (.leaf (-19)) (.branch 13 (.leaf (-18)) (.leaf (-17))))) (.branch 16 (.branch 15 (.leaf (-16)) (.leaf (-15))) (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_009_237 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (1)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_237
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 26 (.leaf (-5)) (.leaf (-6)))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 18 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 28 (.branch 27 (.leaf (-6)) (.leaf (-5))) (.branch 29 (.leaf (-4)) (.leaf (-3)))),
  (.branch 22 (.branch 18 (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))) (.branch 20 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.leaf (-9))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_009_238 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (3))) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (4))) (.branch 14 (.leaf (0)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (5))) (.branch 29 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_238
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-17))),
  (.branch 28 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.leaf (-1)) (.leaf (0))),
  (.branch 21 (.branch 17 (.branch 15 (.branch 14 (.leaf (-17)) (.leaf (-16))) (.branch 16 (.leaf (-15)) (.leaf (-14)))) (.branch 19 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-11)) (.leaf (-10))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_009_239 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (1)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (5))) (.branch 21 (.leaf (1)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (4)))))))
  code := certificateD6_239
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 24 (.branch 20 (.leaf (-14)) (.leaf (-13))) (.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-8)) (.leaf (-4))))),
  (.branch 22 (.branch 18 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 27 (.branch 16 (.leaf (-12)) (.leaf (-11))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-7)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_009_240 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (3)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (5))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_240
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 22 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-3)),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-23)) (.leaf (-22))) (.branch 10 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19))))) (.branch 15 (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_009_241 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (2))) (.branch 10 (.leaf (0)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_241
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 23 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_009_242 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (3)))))))
  code := certificateD6_242
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 26 (.leaf (-11)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 21 (.branch 17 (.leaf (-11)) (.leaf (-10))) (.branch 25 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-4))))),
  (.branch 28 (.branch 27 (.leaf (-14)) (.leaf (-12))) (.branch 29 (.leaf (-10)) (.leaf (-8)))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.leaf (-2)),
  (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_009_243 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (5)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (1))) (.branch 21 (.leaf (4)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (5)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (4)))))))
  code := certificateD6_243
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-23))) (.branch 9 (.leaf (-25)) (.leaf (-27)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 24 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 10 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 23 (.branch 10 (.leaf (-27)) (.leaf (-26))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-14)) (.leaf (-7))))),
  (.branch 25 (.leaf (-12)) (.leaf (-7))),
  (.branch 18 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.branch 22 (.leaf (-3)) (.leaf (-2))) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_009_244 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (3))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (5))) (.branch 21 (.leaf (0)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (1))) (.branch 29 (.leaf (4)) (.leaf (5)))))))
  code := certificateD6_244
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.leaf (0))]
  high := ![(.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.leaf (0))]
def witnessD6_009_245 : CycleWitness 6 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (1))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (5))) (.branch 21 (.leaf (0)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (4)))))))
  code := certificateD6_245
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 18 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_009_246 : CycleWitness 6 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (5)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (2)))))))
  code := certificateD6_246
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-8)) (.leaf (-10)))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 24 (.leaf (-4)) (.branch 28 (.leaf (-3)) (.leaf (-2)))),
  (.branch 26 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 27 (.leaf (-15)) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.branch 23 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 6 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-4)))),
  (.branch 27 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 28 (.leaf (-6)) (.leaf (-3)))),
  (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2)))))]
def witnessD6_009_247 : CycleWitness 6 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (1)) (.leaf (5)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_247
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-5)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-21))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 27 (.leaf (-4)) (.branch 28 (.leaf (-3)) (.leaf (-2)))),
  (.branch 21 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-5)) (.leaf (-4)))),
  (.branch 15 (.leaf (-2)) (.leaf (0))),
  (.branch 18 (.leaf (-7)) (.branch 28 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.branch 20 (.branch 5 (.leaf (-21)) (.leaf (-20))) (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-16)) (.leaf (-14))))) (.branch 26 (.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-8)))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2))))]
def witnessD6_009_248 : CycleWitness 6 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (4))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (3)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (5)))))))
  code := certificateD6_248
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-14)) (.leaf (-18)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 13 (.leaf (-11)) (.leaf (-16))))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 19 (.leaf (-3)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 5 (.leaf (-18)) (.branch 28 (.leaf (-17)) (.leaf (-12)))),
  (.branch 27 (.branch 14 (.leaf (-16)) (.leaf (-15))) (.branch 28 (.leaf (-11)) (.leaf (-7)))),
  (.leaf (-5)),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.leaf (-2)))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-16)) (.leaf (-14))) (.branch 24 (.leaf (-12)) (.leaf (-10)))) (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.leaf (-1)) (.leaf (0)))]
def witnessD6_009_249 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (5))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (4))))))
  code := certificateD6_249
  counts := ![(.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 8 (.leaf (5)) (.leaf (6))) (.branch 10 (.leaf (7)) (.branch 12 (.leaf (8)) (.leaf (9)))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (10)) (.leaf (11))) (.branch 17 (.leaf (12)) (.branch 19 (.leaf (13)) (.leaf (14))))) (.branch 24 (.branch 22 (.leaf (15)) (.branch 23 (.leaf (16)) (.leaf (17)))) (.branch 26 (.leaf (18)) (.branch 27 (.leaf (19)) (.leaf (20))))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 3 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 21 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 25 (.leaf (-6)) (.leaf (-5))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 10 (.leaf (-19)) (.branch 11 (.leaf (-18)) (.leaf (-17))))) (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 21 (.branch 17 (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))) (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.leaf (-8))))) (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_009_250 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 8 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (5)) (.branch 27 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_250
  counts := ![(.branch 13 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))))) (.branch 21 (.branch 16 (.branch 15 (.leaf (9)) (.leaf (10))) (.branch 18 (.leaf (11)) (.branch 19 (.leaf (12)) (.leaf (13))))) (.branch 24 (.branch 22 (.leaf (14)) (.leaf (15))) (.branch 26 (.leaf (16)) (.branch 27 (.leaf (17)) (.leaf (18))))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-10)) (.branch 8 (.leaf (-11)) (.leaf (-12))))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 25 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 23 (.leaf (-12)) (.leaf (-9))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-17)) (.leaf (-16))) (.branch 14 (.leaf (-15)) (.leaf (-14)))) (.branch 17 (.branch 16 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-11)) (.leaf (-10))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_009_251 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (5)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (1)))))))
  code := certificateD6_251
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 15 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 23 (.branch 21 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 5 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 17 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 28 (.leaf (9)) (.leaf (10)))))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 16 (.leaf (-7)) (.branch 18 (.leaf (-8)) (.leaf (-9))))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-18))),
  (.branch 24 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 24 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-6)))),
  (.branch 23 (.branch 20 (.leaf (-3)) (.leaf (-2))) (.branch 26 (.leaf (-1)) (.leaf (0)))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 19 (.branch 14 (.branch 12 (.branch 11 (.leaf (-18)) (.leaf (-17))) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 16 (.branch 15 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_009_252 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (4)) (.leaf (0)))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (5)) (.leaf (0)))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (0)) (.leaf (1)))))))
  code := certificateD6_252
  counts := ![(.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 18 (.leaf (10)) (.leaf (11)))) (.branch 23 (.branch 21 (.leaf (12)) (.leaf (13))) (.branch 25 (.leaf (14)) (.branch 27 (.leaf (15)) (.leaf (16))))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 7 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-18))),
  (.branch 24 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 24 (.branch 22 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 24 (.branch 23 (.leaf (-3)) (.leaf (-2))) (.branch 25 (.leaf (-1)) (.leaf (0)))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.branch 14 (.branch 12 (.branch 11 (.leaf (-18)) (.leaf (-17))) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 16 (.branch 15 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_009_253 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (0)))) (.branch 26 (.leaf (5)) (.branch 27 (.leaf (0)) (.leaf (1)))))))
  code := certificateD6_253
  counts := ![(.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 18 (.leaf (10)) (.leaf (11)))) (.branch 23 (.branch 22 (.leaf (12)) (.leaf (13))) (.branch 25 (.leaf (14)) (.branch 27 (.leaf (15)) (.leaf (16))))))),
  (.branch 14 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 12 (.leaf (0)) (.leaf (-16))),
  (.branch 19 (.leaf (0)) (.leaf (-9))),
  (.branch 26 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 24 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 25 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.branch 10 (.branch 7 (.branch 6 (.leaf (-23)) (.leaf (-22))) (.branch 8 (.leaf (-21)) (.branch 9 (.leaf (-20)) (.leaf (-19))))) (.branch 13 (.branch 11 (.leaf (-18)) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))))) (.branch 22 (.branch 19 (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 20 (.branch 16 (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_009_254 : CycleWitness 6 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (3)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 25 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (0)))) (.branch 26 (.leaf (5)) (.branch 27 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_254
  counts := ![(.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 18 (.leaf (10)) (.leaf (11)))) (.branch 23 (.branch 22 (.leaf (12)) (.leaf (13))) (.branch 25 (.leaf (14)) (.branch 27 (.leaf (15)) (.leaf (16))))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-16))),
  (.branch 26 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 24 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 16 (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_009 : Fin 33 → CycleWitness 6 := ![witnessD6_009_222, witnessD6_009_223, witnessD6_009_224, witnessD6_009_225, witnessD6_009_226, witnessD6_009_227, witnessD6_009_228, witnessD6_009_229, witnessD6_009_230, witnessD6_009_231, witnessD6_009_232, witnessD6_009_233, witnessD6_009_234, witnessD6_009_235, witnessD6_009_236, witnessD6_009_237, witnessD6_009_238, witnessD6_009_239, witnessD6_009_240, witnessD6_009_241, witnessD6_009_242, witnessD6_009_243, witnessD6_009_244, witnessD6_009_245, witnessD6_009_246, witnessD6_009_247, witnessD6_009_248, witnessD6_009_249, witnessD6_009_250, witnessD6_009_251, witnessD6_009_252, witnessD6_009_253, witnessD6_009_254]
end RealPinwheel.FiveSixths


