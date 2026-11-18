-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD5_001
-- name    : RealPinwheel_FiveSixths_WitnessD5_001
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:00:37.912664+00:00
-- url     : https://prove2.me/theorems/52efd3f1-1c53-4740-a28d-3e1f32a0d089
-- title:
--   Exact witness block D5_001
-- statement:
--   These exact witnesses represent words 37 through 86 of source certificate file D5. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D5, entries 37–86; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D5.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD5
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD5_001_36 : CycleWitness 5 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (4)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1)))))))
  code := certificateD5_36
  counts := ![(.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 12 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-13)) (.leaf (-26)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (-1))) (.branch 18 (.leaf (-2)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-9)) (.leaf (-13)))),
  (.branch 23 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 13 (.branch 3 (.leaf (-26)) (.branch 8 (.leaf (-25)) (.leaf (-24)))) (.branch 18 (.leaf (-23)) (.branch 23 (.leaf (-22)) (.leaf (-13))))),
  (.branch 19 (.leaf (-5)) (.branch 22 (.leaf (-4)) (.leaf (0)))),
  (.branch 21 (.branch 20 (.leaf (-13)) (.leaf (-11))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-7)) (.leaf (-5))))),
  (.leaf (-1)),
  (.branch 16 (.branch 12 (.branch 10 (.leaf (-15)) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))))]
def witnessD5_001_37 : CycleWitness 5 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))))))
  code := certificateD5_37
  counts := ![(.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 14 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-18))),
  (.branch 18 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 15 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-4)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 15 (.branch 10 (.branch 8 (.branch 7 (.leaf (-18)) (.leaf (-17))) (.branch 9 (.leaf (-16)) (.leaf (-15)))) (.branch 12 (.branch 11 (.leaf (-14)) (.leaf (-13))) (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_001_38 : CycleWitness 5 where
  length := 24
  word := (.branch 12 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 20 (.leaf (4)) (.leaf (0))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (1)))))))
  code := certificateD5_38
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 14 (.branch 13 (.leaf (7)) (.leaf (8))) (.branch 16 (.leaf (9)) (.leaf (10)))) (.branch 21 (.branch 19 (.leaf (11)) (.leaf (12))) (.branch 23 (.leaf (13)) (.leaf (14)))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 20 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 20 (.leaf (-11)) (.branch 22 (.leaf (-9)) (.leaf (-7)))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-16)) (.leaf (-15))) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_001_39 : CycleWitness 5 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))))))
  code := certificateD5_39
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 13 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 18 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-5)))),
  (.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 16 (.branch 12 (.branch 10 (.leaf (-15)) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_001_40 : CycleWitness 5 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (0)) (.leaf (3)))))))
  code := certificateD5_40
  counts := ![(.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 21 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 23 (.leaf (11)) (.leaf (12)))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 18 (.leaf (-8)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-2)))]
  high := ![(.leaf (-1)),
  (.branch 21 (.branch 19 (.leaf (-10)) (.branch 20 (.leaf (-9)) (.leaf (-8)))) (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 23 (.leaf (-2)) (.leaf (-1)))]
def witnessD5_001_41 : CycleWitness 5 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (4)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (1)))))))
  code := certificateD5_41
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 21 (.leaf (-1)) (.leaf (0))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.branch 12 (.branch 10 (.leaf (-15)) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_001_42 : CycleWitness 5 where
  length := 23
  word := (.branch 13 (.branch 6 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (1)) (.leaf (0))))) (.branch 17 (.branch 14 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (0)) (.leaf (1))))))
  code := certificateD5_42
  counts := ![(.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 8 (.branch 6 (.leaf (4)) (.leaf (5))) (.branch 9 (.leaf (6)) (.leaf (7))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (8)) (.leaf (9))) (.branch 15 (.leaf (10)) (.leaf (11)))) (.branch 19 (.branch 18 (.leaf (12)) (.leaf (13))) (.branch 21 (.leaf (14)) (.branch 22 (.leaf (15)) (.leaf (16))))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 3 (.leaf (-14)) (.branch 13 (.leaf (-21)) (.leaf (-22))))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 20 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 17 (.branch 14 (.leaf (-22)) (.leaf (-20))) (.branch 20 (.leaf (-18)) (.leaf (-16)))),
  (.branch 11 (.leaf (-2)) (.branch 18 (.leaf (-1)) (.leaf (0)))),
  (.branch 21 (.leaf (-3)) (.branch 22 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-16)) (.leaf (-15))) (.branch 10 (.leaf (-14)) (.leaf (-13)))) (.branch 13 (.branch 12 (.leaf (-12)) (.leaf (-11))) (.branch 14 (.leaf (-10)) (.leaf (-9))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-7))) (.branch 18 (.leaf (-6)) (.leaf (-5)))) (.branch 21 (.branch 20 (.leaf (-4)) (.leaf (-3))) (.branch 22 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 16 (.branch 15 (.leaf (-9)) (.leaf (-8))) (.branch 17 (.leaf (-7)) (.leaf (-6)))) (.branch 20 (.branch 19 (.leaf (-5)) (.leaf (-4))) (.branch 21 (.leaf (-3)) (.branch 22 (.leaf (-2)) (.leaf (-1))))))]
def witnessD5_001_43 : CycleWitness 5 where
  length := 22
  word := (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (2))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2))))))
  code := certificateD5_43
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (5)) (.leaf (6))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (7)) (.leaf (8))) (.branch 15 (.leaf (9)) (.leaf (10)))) (.branch 19 (.branch 18 (.leaf (11)) (.leaf (12))) (.branch 21 (.leaf (13)) (.leaf (14)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-8)) (.branch 8 (.leaf (-9)) (.leaf (-10))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 20 (.leaf (-10)) (.leaf (-7))),
  (.branch 15 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-16)) (.leaf (-15))) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_001_44 : CycleWitness 5 where
  length := 22
  word := (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 7 (.leaf (3)) (.leaf (0))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2)))))))
  code := certificateD5_44
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 15 (.branch 12 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))) (.branch 19 (.branch 17 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.leaf (12)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 18 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 16 (.branch 14 (.leaf (-10)) (.leaf (-9))) (.branch 18 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))),
  (.branch 15 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 17 (.leaf (-1)) (.leaf (0))),
  (.branch 14 (.branch 10 (.branch 8 (.leaf (-15)) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_001_45 : CycleWitness 5 where
  length := 22
  word := (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (1)))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (1))))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (1)))))))
  code := certificateD5_45
  counts := ![(.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 12 (.leaf (5)) (.branch 13 (.leaf (6)) (.leaf (7)))) (.branch 18 (.leaf (8)) (.branch 20 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 13 (.leaf (-10)) (.leaf (-11)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-18))),
  (.branch 15 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 14 (.leaf (-11)) (.branch 21 (.leaf (-10)) (.leaf (-6)))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 13 (.branch 8 (.branch 6 (.branch 5 (.leaf (-18)) (.leaf (-17))) (.branch 7 (.leaf (-16)) (.leaf (-15)))) (.branch 10 (.branch 9 (.leaf (-14)) (.leaf (-13))) (.branch 11 (.leaf (-12)) (.branch 12 (.leaf (-11)) (.leaf (-10)))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-9)) (.leaf (-8))) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_001_46 : CycleWitness 5 where
  length := 22
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 8 (.branch 7 (.leaf (2)) (.leaf (0))) (.branch 9 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (4)))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (0))))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (1)))))))
  code := certificateD5_46
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 15 (.branch 11 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))) (.branch 19 (.branch 17 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 11 (.leaf (-10)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 16 (.branch 12 (.leaf (-11)) (.branch 14 (.leaf (-10)) (.leaf (-9)))) (.branch 18 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))),
  (.leaf (0)),
  (.branch 8 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (-3)))),
  (.branch 18 (.branch 4 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7)))) (.branch 20 (.branch 19 (.leaf (-6)) (.leaf (-5))) (.branch 21 (.leaf (-4)) (.leaf (-3))))),
  (.branch 17 (.branch 14 (.branch 13 (.leaf (-10)) (.leaf (-9))) (.branch 15 (.leaf (-8)) (.branch 16 (.leaf (-7)) (.leaf (-6))))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))))]
def witnessD5_001_47 : CycleWitness 5 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (2)))))))
  code := certificateD5_47
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 12 (.leaf (5)) (.branch 14 (.leaf (6)) (.leaf (7)))) (.branch 18 (.leaf (8)) (.branch 20 (.leaf (9)) (.leaf (10)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-6)) (.leaf (-7)))) (.branch 7 (.leaf (-8)) (.branch 9 (.leaf (-9)) (.leaf (-10))))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 15 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-12))),
  (.branch 21 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 21 (.leaf (-10)) (.leaf (-5))),
  (.branch 20 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 16 (.branch 13 (.branch 11 (.leaf (-12)) (.branch 12 (.leaf (-11)) (.leaf (-10)))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD5_001_48 : CycleWitness 5 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (3)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (4)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))))))
  code := certificateD5_48
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 19 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 18 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.leaf (-4)))),
  (.branch 16 (.leaf (-6)) (.branch 19 (.leaf (-5)) (.leaf (-4)))),
  (.branch 17 (.leaf (-1)) (.leaf (0))),
  (.branch 15 (.branch 11 (.branch 9 (.leaf (-14)) (.branch 10 (.leaf (-13)) (.leaf (-12)))) (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.leaf (-8))))) (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_001_49 : CycleWitness 5 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (2)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (2)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (4)))))))
  code := certificateD5_49
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 12 (.leaf (5)) (.branch 14 (.leaf (6)) (.leaf (7)))) (.branch 18 (.leaf (8)) (.branch 21 (.leaf (9)) (.leaf (10)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.branch 7 (.leaf (-8)) (.leaf (-9))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 19 (.leaf (-9)) (.leaf (-5))),
  (.branch 21 (.leaf (-6)) (.leaf (-3))),
  (.branch 20 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (-3)))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD5_001_50 : CycleWitness 5 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (3)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (4)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2)))))))
  code := certificateD5_50
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 19 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 16 (.branch 13 (.leaf (-7)) (.leaf (-6))) (.branch 19 (.leaf (-5)) (.leaf (-4)))),
  (.branch 17 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 19 (.branch 18 (.leaf (-3)) (.leaf (-2))) (.branch 20 (.leaf (-1)) (.leaf (0)))),
  (.branch 15 (.branch 11 (.branch 9 (.leaf (-14)) (.branch 10 (.leaf (-13)) (.leaf (-12)))) (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.leaf (-8))))) (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_001_51 : CycleWitness 5 where
  length := 21
  word := (.branch 11 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (4)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (0))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (4)))))))
  code := certificateD5_51
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 15 (.branch 11 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))) (.branch 18 (.branch 16 (.leaf (9)) (.leaf (10))) (.branch 20 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 17 (.leaf (-6)) (.branch 19 (.leaf (-5)) (.leaf (-4)))),
  (.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.branch 15 (.branch 4 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-12)) (.leaf (-10)))) (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-6))) (.branch 20 (.leaf (-4)) (.leaf (-2))))),
  (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-6))) (.branch 20 (.leaf (-4)) (.leaf (-2)))),
  (.branch 11 (.leaf (-1)) (.leaf (0)))]
def witnessD5_001_52 : CycleWitness 5 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (4)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (2)))))))
  code := certificateD5_52
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-9)) (.leaf (-15)))),
  (.branch 18 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 18 (.leaf (-5)) (.leaf (-3))),
  (.branch 20 (.leaf (-4)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11))))) (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_001_53 : CycleWitness 5 where
  length := 20
  word := (.branch 10 (.branch 6 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (2))))) (.branch 16 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (4)) (.branch 19 (.leaf (0)) (.leaf (2))))))
  code := certificateD5_53
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (5)) (.leaf (6))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (7)) (.leaf (8))) (.branch 13 (.leaf (9)) (.leaf (10)))) (.branch 18 (.branch 16 (.leaf (11)) (.leaf (12))) (.branch 19 (.leaf (13)) (.leaf (14)))))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 3 (.leaf (-6)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 17 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 14 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7)))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-13)) (.branch 9 (.leaf (-12)) (.leaf (-11)))) (.branch 11 (.leaf (-10)) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_001_54 : CycleWitness 5 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (4)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (1)))))))
  code := certificateD5_54
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 11 (.leaf (5)) (.branch 12 (.leaf (6)) (.leaf (7)))) (.branch 16 (.leaf (8)) (.branch 18 (.leaf (9)) (.leaf (10)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_001_55 : CycleWitness 5 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (1)))))))
  code := certificateD5_55
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 15 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 16 (.leaf (-11)) (.branch 19 (.leaf (-10)) (.leaf (-7)))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 18 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD5_001_56 : CycleWitness 5 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (3))) (.branch 9 (.leaf (0)) (.leaf (1))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (1))))))
  code := certificateD5_56
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 14 (.branch 11 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))) (.branch 17 (.branch 16 (.leaf (9)) (.leaf (10))) (.branch 19 (.leaf (11)) (.leaf (12)))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 18 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-12)) (.branch 10 (.leaf (-11)) (.leaf (-10)))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1)))]
def witnessD5_001_57 : CycleWitness 5 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (4)))))))
  code := certificateD5_57
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 19 (.leaf (-4)) (.leaf (-2))),
  (.leaf (-2)),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD5_001_58 : CycleWitness 5 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (4))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))))))
  code := certificateD5_58
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 17 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 19 (.leaf (-4)) (.leaf (-2))),
  (.branch 16 (.leaf (-5)) (.leaf (-3))),
  (.branch 15 (.leaf (-1)) (.leaf (0))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-13)) (.branch 9 (.leaf (-12)) (.leaf (-11)))) (.branch 11 (.leaf (-10)) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_001_59 : CycleWitness 5 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (3)))))))
  code := certificateD5_59
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 17 (.leaf (-3)) (.leaf (-2))),
  (.branch 13 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_001_60 : CycleWitness 5 where
  length := 19
  word := (.branch 10 (.branch 5 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 8 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 9 (.leaf (1)) (.leaf (0))))) (.branch 14 (.branch 11 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (4)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.leaf (1))))))
  code := certificateD5_60
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 13 (.branch 10 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))) (.branch 16 (.branch 15 (.leaf (9)) (.leaf (10))) (.branch 18 (.leaf (11)) (.leaf (12)))))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 3 (.leaf (-6)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-11)))),
  (.branch 14 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 4 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-6)))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 7 (.leaf (-4)) (.branch 18 (.leaf (-3)) (.leaf (-2)))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.leaf (-8)))) (.branch 17 (.branch 16 (.leaf (-7)) (.leaf (-6))) (.branch 18 (.leaf (-5)) (.leaf (-4))))),
  (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_001_61 : CycleWitness 5 where
  length := 19
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (1)))))))
  code := certificateD5_61
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 10 (.leaf (5)) (.branch 12 (.leaf (6)) (.leaf (7)))) (.branch 16 (.leaf (8)) (.branch 18 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-9)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 15 (.leaf (-7)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.branch 17 (.leaf (-1)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 9 (.branch 5 (.branch 3 (.leaf (-18)) (.leaf (-17))) (.branch 7 (.leaf (-16)) (.leaf (-15)))) (.branch 13 (.branch 11 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 17 (.leaf (-11)) (.leaf (-10)))))),
  (.leaf (0)),
  (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))),
  (.branch 18 (.leaf (-7)) (.leaf (-6))),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-16)) (.leaf (-15))) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))))]
def witnessD5_001_62 : CycleWitness 5 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (4)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1)))))))
  code := certificateD5_62
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-13)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 16 (.leaf (-8)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 13 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 12 (.branch 6 (.leaf (-17)) (.branch 9 (.leaf (-16)) (.leaf (-15)))) (.branch 15 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-8))))),
  (.branch 3 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (0)))),
  (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.branch 8 (.leaf (-3)) (.leaf (-2))),
  (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_001_63 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 6 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 15 (.branch 12 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (2))))))
  code := certificateD5_63
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (3)) (.branch 6 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (8)))) (.branch 15 (.branch 14 (.leaf (9)) (.leaf (10))) (.branch 17 (.leaf (11)) (.leaf (12)))))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-1))) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 16 (.leaf (-3)) (.leaf (-2))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.leaf (-2)) (.leaf (-1)))]
def witnessD5_001_64 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (3))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3)))))))
  code := certificateD5_64
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 15 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.leaf (-4)) (.leaf (-2))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_001_65 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (1)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (4))) (.branch 17 (.leaf (0)) (.leaf (2))))))
  code := certificateD5_65
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 10 (.leaf (5)) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 15 (.leaf (8)) (.branch 17 (.leaf (9)) (.leaf (10)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 14 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 6 (.leaf (-1)) (.leaf (0))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.leaf (-2)) (.leaf (-1)))]
def witnessD5_001_66 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (2)))))))
  code := certificateD5_66
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_001_67 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (3)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))))))
  code := certificateD5_67
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 4 (.leaf (-8)) (.leaf (-9)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 13 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 12 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-5)))),
  (.branch 14 (.leaf (-7)) (.leaf (-5))),
  (.branch 16 (.branch 6 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_001_68 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (4)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.leaf (2))))))
  code := certificateD5_68
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 10 (.leaf (5)) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 15 (.leaf (8)) (.branch 17 (.leaf (9)) (.leaf (10)))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 14 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))),
  (.branch 17 (.leaf (-4)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_001_69 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (4))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1)))))))
  code := certificateD5_69
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 14 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.leaf (-5)))),
  (.branch 4 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (0)))),
  (.branch 13 (.leaf (-6)) (.leaf (-5))),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-12)) (.branch 8 (.leaf (-11)) (.leaf (-10)))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_001_70 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (2)) (.leaf (1))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (4)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (2)) (.leaf (1))))))
  code := certificateD5_70
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 13 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 12 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-5)))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_001_71 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (4))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))))))
  code := certificateD5_71
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 14 (.branch 3 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.leaf (-5)))),
  (.branch 7 (.leaf (-6)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 16 (.branch 5 (.leaf (-6)) (.leaf (-5))) (.branch 17 (.leaf (-4)) (.leaf (-3)))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD5_001_72 : CycleWitness 5 where
  length := 18
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (3))) (.branch 9 (.leaf (0)) (.leaf (1))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (4)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.leaf (3))))))
  code := certificateD5_72
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 9 (.leaf (5)) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 15 (.leaf (8)) (.branch 17 (.leaf (9)) (.leaf (10)))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-10)) (.leaf (-13)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 12 (.branch 8 (.leaf (-13)) (.branch 10 (.leaf (-12)) (.leaf (-11)))) (.branch 14 (.leaf (-10)) (.branch 16 (.leaf (-9)) (.leaf (-8))))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_001_73 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (4)))))))
  code := certificateD5_73
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 15 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-12)) (.branch 8 (.leaf (-11)) (.leaf (-10)))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_001_74 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))))))
  code := certificateD5_74
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 4 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-7)))),
  (.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.branch 6 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD5_001_75 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (2)))))))
  code := certificateD5_75
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 15 (.leaf (-7)) (.leaf (-4))),
  (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.leaf (-2)) (.leaf (-1)))]
def witnessD5_001_76 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (4)))))))
  code := certificateD5_76
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-7)))),
  (.leaf (0))]
  high := ![(.branch 15 (.leaf (-7)) (.leaf (-4))),
  (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 14 (.leaf (-7)) (.leaf (-6))) (.branch 16 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (0))]
def witnessD5_001_77 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (2)))))))
  code := certificateD5_77
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 10 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 13 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 11 (.leaf (-7)) (.leaf (-6))) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 9 (.leaf (-2)) (.branch 14 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_001_78 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))))))
  code := certificateD5_78
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 13 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.leaf (-9)) (.branch 14 (.leaf (-7)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_001_79 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (2)))))))
  code := certificateD5_79
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-2)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 15 (.leaf (-7)) (.leaf (-4))),
  (.branch 16 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.leaf (-2)) (.leaf (-1)))]
def witnessD5_001_80 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))))))
  code := certificateD5_80
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 5 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 14 (.branch 6 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-11)) (.leaf (-6)))),
  (.branch 3 (.leaf (-5)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 16 (.branch 5 (.leaf (-6)) (.leaf (-5))) (.branch 17 (.leaf (-4)) (.leaf (-3)))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD5_001_81 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (4))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1)))))))
  code := certificateD5_81
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.leaf (-1)) (.leaf (0))),
  (.branch 13 (.leaf (-3)) (.leaf (-2))),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-12)) (.branch 8 (.leaf (-11)) (.leaf (-10)))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_001_82 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (2)))))))
  code := certificateD5_82
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.branch 5 (.leaf (-1)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 16 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 17 (.leaf (-10)) (.leaf (-5)))),
  (.branch 3 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-5)))),
  (.branch 15 (.branch 10 (.leaf (-3)) (.leaf (-2))) (.branch 16 (.leaf (-1)) (.leaf (0)))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_001_83 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (4)))))))
  code := certificateD5_83
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.leaf (0))]
  high := ![(.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.leaf (-9)) (.branch 14 (.leaf (-7)) (.leaf (-5)))),
  (.branch 12 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-5)))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD5_001_84 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (4)))))))
  code := certificateD5_84
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.leaf (0))]
  high := ![(.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.leaf (0))]
def witnessD5_001_85 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))))))
  code := certificateD5_85
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 3 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-5)))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 6 (.leaf (-1)) (.leaf (0))),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 11 (.leaf (-8)) (.branch 12 (.leaf (-7)) (.leaf (-6))))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD5_001 : Fin 50 → CycleWitness 5 := ![witnessD5_001_36, witnessD5_001_37, witnessD5_001_38, witnessD5_001_39, witnessD5_001_40, witnessD5_001_41, witnessD5_001_42, witnessD5_001_43, witnessD5_001_44, witnessD5_001_45, witnessD5_001_46, witnessD5_001_47, witnessD5_001_48, witnessD5_001_49, witnessD5_001_50, witnessD5_001_51, witnessD5_001_52, witnessD5_001_53, witnessD5_001_54, witnessD5_001_55, witnessD5_001_56, witnessD5_001_57, witnessD5_001_58, witnessD5_001_59, witnessD5_001_60, witnessD5_001_61, witnessD5_001_62, witnessD5_001_63, witnessD5_001_64, witnessD5_001_65, witnessD5_001_66, witnessD5_001_67, witnessD5_001_68, witnessD5_001_69, witnessD5_001_70, witnessD5_001_71, witnessD5_001_72, witnessD5_001_73, witnessD5_001_74, witnessD5_001_75, witnessD5_001_76, witnessD5_001_77, witnessD5_001_78, witnessD5_001_79, witnessD5_001_80, witnessD5_001_81, witnessD5_001_82, witnessD5_001_83, witnessD5_001_84, witnessD5_001_85]
end RealPinwheel.FiveSixths


