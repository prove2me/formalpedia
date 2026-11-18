-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_065
-- name    : RealPinwheel_FiveSixths_WitnessD7_065
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:17:39.989207+00:00
-- url     : https://prove2.me/theorems/b20b76e1-32e1-48cd-9026-ac895daf5418
-- title:
--   Exact witness block D7_065
-- statement:
--   These exact witnesses represent words 1268 through 1305 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 1268–1305; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_065_1267 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (6)) (.leaf (0)))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1267
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (7)) (.leaf (8))) (.branch 17 (.leaf (9)) (.leaf (10)))) (.branch 23 (.branch 21 (.leaf (11)) (.leaf (12))) (.branch 25 (.leaf (13)) (.leaf (14)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 24 (.leaf (-8)) (.leaf (-7))))),
  (.branch 25 (.leaf (-6)) (.leaf (-3))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 12 (.leaf (-15)) (.leaf (-14)))) (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_065_1268 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 11 (.leaf (3)) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (6))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1268
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (7)) (.leaf (8))) (.branch 17 (.leaf (9)) (.leaf (10)))) (.branch 23 (.branch 21 (.leaf (11)) (.leaf (12))) (.branch 25 (.leaf (13)) (.leaf (14)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 11 (.leaf (0)) (.leaf (-15))),
  (.branch 24 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 24 (.leaf (-8)) (.leaf (-7))))),
  (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 20 (.branch 19 (.leaf (-3)) (.leaf (-2))) (.branch 21 (.leaf (-1)) (.leaf (0)))),
  (.branch 18 (.branch 14 (.branch 12 (.leaf (-15)) (.branch 13 (.leaf (-14)) (.leaf (-13)))) (.branch 16 (.branch 15 (.leaf (-12)) (.leaf (-11))) (.branch 17 (.leaf (-10)) (.leaf (-9))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.branch 11 (.branch 9 (.branch 8 (.leaf (-19)) (.leaf (-18))) (.branch 10 (.leaf (-17)) (.leaf (-16)))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_065_1269 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (0))))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (0))) (.branch 23 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1269
  counts := ![(.branch 12 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (8)) (.leaf (9))) (.branch 17 (.leaf (10)) (.leaf (11)))) (.branch 22 (.branch 20 (.leaf (12)) (.leaf (13))) (.branch 24 (.leaf (14)) (.branch 25 (.leaf (15)) (.leaf (16))))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 16 (.leaf (-10)) (.branch 21 (.leaf (-9)) (.leaf (-8)))),
  (.branch 24 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 10 (.branch 7 (.branch 6 (.leaf (-21)) (.leaf (-20))) (.branch 8 (.leaf (-19)) (.branch 9 (.leaf (-18)) (.leaf (-17))))) (.branch 12 (.branch 11 (.leaf (-16)) (.leaf (-15))) (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7))))) (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_065_1270 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (3)) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (2)) (.leaf (1)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (4)) (.branch 19 (.leaf (1)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (6)) (.branch 22 (.leaf (0)) (.leaf (1)))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (1)))))))
  code := certificateD7_1270
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 22 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 24 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))) (.branch 15 (.leaf (-11)) (.branch 17 (.leaf (-12)) (.leaf (-13))))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 18 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-8)))),
  (.branch 20 (.leaf (-2)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 15 (.branch 10 (.branch 7 (.branch 6 (.leaf (-21)) (.leaf (-20))) (.branch 8 (.leaf (-19)) (.branch 9 (.leaf (-18)) (.leaf (-17))))) (.branch 12 (.branch 11 (.leaf (-16)) (.leaf (-15))) (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7))))) (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_065_1271 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (2)) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1271
  counts := ![(.branch 12 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.leaf (7))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (8)) (.leaf (9))) (.branch 17 (.leaf (10)) (.leaf (11)))) (.branch 22 (.branch 20 (.leaf (12)) (.leaf (13))) (.branch 23 (.leaf (14)) (.branch 25 (.leaf (15)) (.leaf (16))))))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 10 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 24 (.leaf (-11)) (.leaf (-8))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 15 (.branch 10 (.branch 7 (.branch 6 (.leaf (-21)) (.leaf (-20))) (.branch 8 (.leaf (-19)) (.branch 9 (.leaf (-18)) (.leaf (-17))))) (.branch 12 (.branch 11 (.leaf (-16)) (.leaf (-15))) (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7))))) (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_065_1272 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 11 (.leaf (4)) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1272
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 22 (.leaf (9)) (.branch 25 (.leaf (10)) (.leaf (11)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-13)) (.leaf (-26)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 19 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 13 (.branch 3 (.leaf (-26)) (.branch 8 (.leaf (-25)) (.leaf (-24)))) (.branch 18 (.leaf (-23)) (.branch 23 (.leaf (-22)) (.leaf (-17))))),
  (.branch 17 (.branch 10 (.leaf (-8)) (.leaf (-7))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 20 (.branch 19 (.leaf (-3)) (.leaf (-2))) (.branch 21 (.leaf (-1)) (.leaf (0)))),
  (.branch 23 (.branch 22 (.leaf (-15)) (.leaf (-12))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_065_1273 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (5)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (0)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (6)) (.leaf (1)))))))
  code := certificateD7_1273
  counts := ![(.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 13 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-5)) (.leaf (-8)))),
  (.branch 12 (.leaf (0)) (.leaf (-14))),
  (.branch 25 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 22 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.leaf (-5)))),
  (.branch 19 (.branch 15 (.leaf (-6)) (.leaf (-4))) (.branch 23 (.leaf (-2)) (.leaf (0)))),
  (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 24 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-3))))),
  (.branch 19 (.branch 15 (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))) (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_065_1274 : CycleWitness 7 where
  length := 26
  word := (.branch 14 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (5)) (.leaf (0))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 23 (.branch 20 (.leaf (2)) (.branch 22 (.leaf (0)) (.leaf (4)))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1274
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))) (.branch 22 (.branch 21 (.leaf (10)) (.leaf (11))) (.branch 25 (.leaf (12)) (.leaf (13)))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 15 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-15)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7))))) (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_065_1275 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (0)))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1275
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (7)) (.leaf (8))) (.branch 17 (.leaf (9)) (.leaf (10)))) (.branch 23 (.branch 21 (.leaf (11)) (.leaf (12))) (.branch 25 (.leaf (13)) (.leaf (14)))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 20 (.branch 16 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 24 (.leaf (-8)) (.leaf (-7))))),
  (.branch 25 (.leaf (-4)) (.leaf (-2))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_065_1276 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1276
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 23 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 25 (.leaf (11)) (.leaf (12)))))),
  (.branch 11 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-8)) (.branch 7 (.leaf (-9)) (.leaf (-10))))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 21 (.leaf (-10)) (.leaf (-6))),
  (.branch 18 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 16 (.branch 11 (.branch 8 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 9 (.leaf (-18)) (.branch 10 (.leaf (-17)) (.leaf (-16))))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 12 (.leaf (-15)) (.leaf (-14)))) (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_065_1277 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (6)) (.leaf (1)))))))
  code := certificateD7_1277
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 17 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4))),
  (.branch 12 (.leaf (0)) (.leaf (-14))),
  (.branch 25 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 22 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 21 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.leaf (0)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 12 (.leaf (-15)) (.leaf (-14)))) (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.branch 15 (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))) (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_065_1278 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (6)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1278
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 23 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 25 (.leaf (11)) (.leaf (12)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-8)) (.branch 7 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 21 (.leaf (-10)) (.leaf (-6))),
  (.branch 23 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 18 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_065_1279 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1279
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 23 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 25 (.leaf (11)) (.leaf (12)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-8)) (.branch 7 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-14)) (.leaf (-15)))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 24 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 21 (.leaf (-10)) (.leaf (-6))),
  (.branch 23 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.branch 22 (.leaf (-15)) (.leaf (-12))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 9 (.leaf (-2)) (.branch 18 (.leaf (-1)) (.leaf (0)))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 14 (.branch 12 (.leaf (-15)) (.branch 13 (.leaf (-14)) (.leaf (-13)))) (.branch 16 (.branch 15 (.leaf (-12)) (.leaf (-11))) (.branch 17 (.leaf (-10)) (.leaf (-9))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_065_1280 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1280
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 22 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 19 (.leaf (-6)) (.leaf (-4))),
  (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.branch 11 (.branch 9 (.branch 8 (.leaf (-19)) (.leaf (-18))) (.branch 10 (.leaf (-17)) (.leaf (-16)))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_065_1281 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (6)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1281
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-16))),
  (.branch 23 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 22 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 19 (.leaf (-6)) (.leaf (-4))),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 18 (.branch 14 (.branch 12 (.branch 11 (.leaf (-16)) (.leaf (-15))) (.branch 13 (.leaf (-14)) (.leaf (-13)))) (.branch 16 (.branch 15 (.leaf (-12)) (.leaf (-11))) (.branch 17 (.leaf (-10)) (.leaf (-9))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_065_1282 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (6)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (4)))))))
  code := certificateD7_1282
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 18 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-14)) (.leaf (-16)))),
  (.branch 17 (.leaf (0)) (.branch 25 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 17 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 24 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.leaf (-4)))),
  (.branch 23 (.branch 13 (.leaf (-16)) (.branch 22 (.leaf (-15)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-2)),
  (.leaf (0)),
  (.branch 16 (.branch 11 (.branch 9 (.branch 8 (.leaf (-19)) (.leaf (-18))) (.branch 10 (.leaf (-17)) (.leaf (-16)))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_065_1283 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1283
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 17 (.leaf (-14)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 22 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 24 (.branch 18 (.leaf (-16)) (.leaf (-13))) (.branch 25 (.leaf (-9)) (.leaf (-5)))),
  (.branch 5 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (0)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 12 (.leaf (-15)) (.leaf (-14)))) (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_065_1284 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1284
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-17)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.leaf (-12))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 19 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 13 (.branch 7 (.branch 4 (.leaf (-25)) (.leaf (-24))) (.branch 10 (.leaf (-23)) (.leaf (-22)))) (.branch 19 (.branch 16 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 25 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 12 (.branch 3 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.leaf (-7)))),
  (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_065_1285 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (6))) (.branch 25 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1285
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 22 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 25 (.leaf (11)) (.leaf (12)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-8)))) (.branch 7 (.leaf (-9)) (.branch 9 (.leaf (-10)) (.leaf (-11))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-15))),
  (.branch 24 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 23 (.leaf (-11)) (.leaf (-6))),
  (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 14 (.branch 12 (.leaf (-15)) (.branch 13 (.leaf (-14)) (.leaf (-13)))) (.branch 16 (.branch 15 (.leaf (-12)) (.leaf (-11))) (.branch 17 (.leaf (-10)) (.leaf (-9))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_065_1286 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1286
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))),
  (.branch 14 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-17)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-8)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 13 (.branch 7 (.branch 4 (.leaf (-25)) (.leaf (-24))) (.branch 10 (.leaf (-23)) (.leaf (-22)))) (.branch 19 (.branch 16 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 25 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 20 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 23 (.leaf (-10)) (.leaf (-9)))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_065_1287 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (2)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (6)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1287
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 24 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 25 (.leaf (-8)) (.leaf (-5)))),
  (.branch 20 (.leaf (-8)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 19 (.leaf (-3)) (.leaf (-2))),
  (.branch 23 (.branch 5 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_065_1288 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (6))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (0)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1288
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-17)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-12)) (.leaf (-19)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-3)) (.leaf (-6))))]
  high := ![(.branch 13 (.branch 7 (.branch 4 (.leaf (-25)) (.leaf (-24))) (.branch 10 (.leaf (-23)) (.leaf (-22)))) (.branch 19 (.branch 16 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 25 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 15 (.branch 6 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.branch 25 (.leaf (-12)) (.leaf (-7))))),
  (.branch 8 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 23 (.leaf (-6)) (.leaf (-5))) (.branch 25 (.leaf (-4)) (.leaf (-3))))]
def witnessD7_065_1289 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1289
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-5)) (.branch 24 (.leaf (-7)) (.leaf (-8))))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 25 (.leaf (-8)) (.leaf (-5))),
  (.branch 17 (.leaf (-4)) (.leaf (-3))),
  (.branch 16 (.branch 11 (.branch 8 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 9 (.leaf (-18)) (.branch 10 (.leaf (-17)) (.leaf (-16))))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_065_1290 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1290
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 8 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 21 (.leaf (-11)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 22 (.leaf (-7)) (.leaf (-4))),
  (.branch 24 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_065_1291 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1291
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 7 (.leaf (-18)) (.branch 23 (.leaf (-20)) (.leaf (-23))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 8 (.leaf (-13)) (.leaf (-17)))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-15)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.branch 25 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 24 (.leaf (-23)) (.branch 25 (.leaf (-16)) (.leaf (-9)))),
  (.branch 17 (.branch 9 (.leaf (-17)) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 21 (.leaf (-14)) (.branch 25 (.leaf (-13)) (.leaf (-8))))),
  (.branch 23 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 24 (.leaf (-11)) (.branch 25 (.leaf (-8)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_065_1292 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (6)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1292
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 25 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 20 (.leaf (-9)) (.branch 23 (.leaf (-7)) (.leaf (-5)))),
  (.branch 16 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_065_1293 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (6))) (.branch 25 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1293
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 25 (.leaf (9)) (.leaf (10)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-15))),
  (.branch 24 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 23 (.leaf (-7)) (.leaf (-5)))),
  (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 22 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-1)) (.leaf (0)))),
  (.branch 15 (.branch 10 (.branch 7 (.branch 6 (.leaf (-21)) (.leaf (-20))) (.branch 8 (.leaf (-19)) (.branch 9 (.leaf (-18)) (.leaf (-17))))) (.branch 12 (.branch 11 (.leaf (-16)) (.leaf (-15))) (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7))))) (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 14 (.branch 12 (.leaf (-15)) (.branch 13 (.leaf (-14)) (.leaf (-13)))) (.branch 16 (.branch 15 (.leaf (-12)) (.leaf (-11))) (.branch 17 (.leaf (-10)) (.leaf (-9))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_065_1294 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (4)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1294
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 20 (.leaf (-8)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 22 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-1)) (.leaf (0)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 12 (.leaf (-15)) (.leaf (-14)))) (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_065_1295 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1295
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 15 (.leaf (-24)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.leaf (-12))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 20 (.branch 16 (.leaf (-25)) (.leaf (-23))) (.branch 24 (.leaf (-21)) (.branch 25 (.leaf (-14)) (.leaf (-7))))),
  (.branch 18 (.branch 3 (.leaf (-12)) (.leaf (-11))) (.branch 22 (.leaf (-9)) (.leaf (-7)))),
  (.branch 25 (.leaf (-6)) (.leaf (-3))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_065_1296 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (3)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (3)) (.leaf (6)))))))
  code := certificateD7_1296
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 24 (.leaf (-3)) (.leaf (-4)))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.leaf (-3)) (.leaf (-2))),
  (.branch 25 (.leaf (-4)) (.leaf (-3))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_065_1297 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (6)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (6)) (.leaf (4)))))))
  code := certificateD7_1297
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 21 (.leaf (-11)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_065_1298 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (6))) (.branch 25 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1298
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 25 (.leaf (9)) (.leaf (10)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-15))),
  (.branch 24 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 23 (.leaf (-7)) (.leaf (-5)))),
  (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.branch 22 (.leaf (-6)) (.leaf (-5))) (.branch 24 (.leaf (-4)) (.branch 25 (.leaf (-3)) (.leaf (-2))))),
  (.branch 17 (.leaf (-2)) (.branch 18 (.leaf (-1)) (.leaf (0)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 14 (.branch 12 (.leaf (-15)) (.branch 13 (.leaf (-14)) (.leaf (-13)))) (.branch 16 (.branch 15 (.leaf (-12)) (.leaf (-11))) (.branch 17 (.leaf (-10)) (.leaf (-9))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_065_1299 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (5)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (1)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (6))) (.branch 25 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1299
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 18 (.leaf (-6)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-8)) (.leaf (-9)))),
  (.branch 12 (.leaf (0)) (.leaf (-14))),
  (.branch 24 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 11 (.branch 5 (.branch 2 (.leaf (-17)) (.leaf (-16))) (.branch 8 (.leaf (-15)) (.leaf (-14)))) (.branch 17 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-9)))))),
  (.branch 24 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.leaf (-4)))),
  (.branch 21 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-2)) (.leaf (0)))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 15 (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))) (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_065_1300 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (6)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1300
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-8)) (.leaf (-11))))]
  high := ![(.branch 11 (.branch 5 (.branch 2 (.leaf (-17)) (.leaf (-16))) (.branch 8 (.leaf (-15)) (.leaf (-14)))) (.branch 17 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-9)))))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-15)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 15 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.leaf (-8)))) (.branch 23 (.branch 22 (.leaf (-7)) (.leaf (-6))) (.branch 24 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-3))))))]
def witnessD7_065_1301 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (5)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1301
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 15 (.leaf (-24)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.leaf (-12))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 20 (.branch 16 (.leaf (-25)) (.leaf (-23))) (.branch 24 (.leaf (-21)) (.branch 25 (.leaf (-14)) (.leaf (-7))))),
  (.branch 18 (.branch 3 (.leaf (-12)) (.leaf (-11))) (.branch 22 (.leaf (-9)) (.leaf (-7)))),
  (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_065_1302 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (4)))))))
  code := certificateD7_1302
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 11 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 25 (.leaf (-10)) (.leaf (-5))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-15)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 8 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_065_1303 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (2)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (3))) (.branch 25 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1303
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 21 (.leaf (-5)) (.leaf (-3))),
  (.branch 18 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_065_1304 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (6)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (6)) (.leaf (4)))))))
  code := certificateD7_1304
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-14)) (.leaf (-15)))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 20 (.leaf (-8)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.branch 22 (.leaf (-15)) (.leaf (-12))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 9 (.leaf (-2)) (.branch 18 (.leaf (-1)) (.leaf (0)))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_065 : Fin 38 → CycleWitness 7 := ![witnessD7_065_1267, witnessD7_065_1268, witnessD7_065_1269, witnessD7_065_1270, witnessD7_065_1271, witnessD7_065_1272, witnessD7_065_1273, witnessD7_065_1274, witnessD7_065_1275, witnessD7_065_1276, witnessD7_065_1277, witnessD7_065_1278, witnessD7_065_1279, witnessD7_065_1280, witnessD7_065_1281, witnessD7_065_1282, witnessD7_065_1283, witnessD7_065_1284, witnessD7_065_1285, witnessD7_065_1286, witnessD7_065_1287, witnessD7_065_1288, witnessD7_065_1289, witnessD7_065_1290, witnessD7_065_1291, witnessD7_065_1292, witnessD7_065_1293, witnessD7_065_1294, witnessD7_065_1295, witnessD7_065_1296, witnessD7_065_1297, witnessD7_065_1298, witnessD7_065_1299, witnessD7_065_1300, witnessD7_065_1301, witnessD7_065_1302, witnessD7_065_1303, witnessD7_065_1304]
end RealPinwheel.FiveSixths


