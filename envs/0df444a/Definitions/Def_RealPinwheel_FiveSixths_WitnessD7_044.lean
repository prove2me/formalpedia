-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_044
-- name    : RealPinwheel_FiveSixths_WitnessD7_044
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:52:15.092241+00:00
-- url     : https://prove2.me/theorems/7359867a-fba3-4564-a071-dbc89291f1c0
-- title:
--   Exact witness block D7_044
-- statement:
--   These exact witnesses represent words 650 through 674 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 650–674; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_044_649 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (1)))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (2)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (6)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (4)) (.leaf (1)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (5)) (.leaf (1))))))))
  code := certificateD7_649
  counts := ![(.branch 18 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))))) (.branch 28 (.branch 22 (.branch 21 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.branch 26 (.leaf (13)) (.leaf (14))))) (.branch 34 (.branch 31 (.leaf (15)) (.branch 32 (.leaf (16)) (.leaf (17)))) (.branch 36 (.leaf (18)) (.branch 38 (.leaf (19)) (.leaf (20))))))),
  (.branch 20 (.branch 10 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-31))),
  (.branch 29 (.leaf (0)) (.leaf (-11))),
  (.branch 39 (.leaf (0)) (.leaf (-1))),
  (.branch 19 (.leaf (0)) (.leaf (-21)))]
  high := ![(.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.leaf (-1)) (.leaf (0))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.leaf (-31)) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17))))) (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_044_650 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (2)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (4))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (5))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (6))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_650
  counts := ![(.branch 19 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))))) (.branch 29 (.branch 22 (.branch 21 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.branch 26 (.leaf (13)) (.leaf (14))))) (.branch 34 (.branch 31 (.leaf (15)) (.branch 32 (.leaf (16)) (.leaf (17)))) (.branch 36 (.leaf (18)) (.branch 39 (.leaf (19)) (.leaf (20))))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-33))),
  (.branch 17 (.leaf (0)) (.leaf (-23))),
  (.branch 27 (.leaf (0)) (.leaf (-13))),
  (.branch 37 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 37 (.leaf (-2)) (.leaf (-1))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 23 (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-33)) (.leaf (-32))) (.branch 10 (.leaf (-31)) (.leaf (-30)))) (.branch 13 (.branch 12 (.leaf (-29)) (.leaf (-28))) (.branch 14 (.leaf (-27)) (.leaf (-26))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-25)) (.leaf (-24))) (.branch 18 (.leaf (-23)) (.leaf (-22)))) (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.leaf (-18)))))) (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 28 (.branch 22 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_044_651 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (4)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (5)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (3)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (1)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.leaf (4)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (6)) (.leaf (1))))))))
  code := certificateD7_651
  counts := ![(.branch 18 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))))) (.branch 28 (.branch 22 (.branch 21 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.branch 26 (.leaf (13)) (.leaf (14))))) (.branch 34 (.branch 31 (.leaf (15)) (.branch 32 (.leaf (16)) (.leaf (17)))) (.branch 36 (.leaf (18)) (.branch 38 (.leaf (19)) (.leaf (20))))))),
  (.branch 20 (.branch 10 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 9 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 19 (.leaf (0)) (.leaf (-21))),
  (.branch 39 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.leaf (-1)) (.leaf (0))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17))))) (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_044_652 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (4))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (6)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (4))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_652
  counts := ![(.branch 18 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 22 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 25 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 35 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))) (.branch 22 (.leaf (-11)) (.branch 35 (.leaf (-14)) (.leaf (-15))))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-30))),
  (.branch 30 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 36 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-11)))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.leaf (-30)) (.branch 12 (.leaf (-29)) (.leaf (-28)))) (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.leaf (-20)))) (.branch 23 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.leaf (-16)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_044_653 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (0))) (.branch 18 (.leaf (6)) (.branch 19 (.leaf (1)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (4)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (5)) (.branch 29 (.leaf (0)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (0))) (.branch 38 (.leaf (6)) (.branch 39 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_653
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 22 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 25 (.leaf (9)) (.leaf (10)))) (.branch 34 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 37 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 22 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-19)) (.leaf (-22)))),
  (.branch 10 (.leaf (0)) (.branch 36 (.leaf (-7)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-1)),
  (.branch 27 (.leaf (-2)) (.branch 34 (.leaf (-1)) (.leaf (0)))),
  (.branch 34 (.branch 31 (.branch 17 (.leaf (-22)) (.leaf (-21))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-17)) (.leaf (-15))))) (.branch 37 (.branch 35 (.leaf (-13)) (.branch 36 (.leaf (-11)) (.leaf (-9)))) (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-7))) (.branch 39 (.leaf (-5)) (.leaf (-3)))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_044_654 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (3))) (.branch 9 (.leaf (0)) (.leaf (4))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (5)))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (0)) (.leaf (4))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (0)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_654
  counts := ![(.branch 19 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 14 (.branch 11 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))) (.branch 16 (.leaf (9)) (.branch 17 (.leaf (10)) (.leaf (11)))))) (.branch 29 (.branch 24 (.branch 21 (.leaf (12)) (.branch 22 (.leaf (13)) (.leaf (14)))) (.branch 26 (.leaf (15)) (.branch 27 (.leaf (16)) (.leaf (17))))) (.branch 34 (.branch 31 (.leaf (18)) (.branch 32 (.leaf (19)) (.leaf (20)))) (.branch 37 (.branch 36 (.leaf (21)) (.leaf (22))) (.branch 39 (.leaf (23)) (.leaf (24))))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.leaf (0))]
  high := ![(.branch 38 (.leaf (-4)) (.leaf (-3))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_044_655 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (4))) (.branch 9 (.leaf (0)) (.leaf (1))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (5))) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1)))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (6))) (.branch 34 (.leaf (0)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (0)) (.leaf (1)))))))
  code := certificateD7_655
  counts := ![(.branch 19 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 14 (.branch 11 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))) (.branch 16 (.leaf (9)) (.branch 17 (.leaf (10)) (.leaf (11)))))) (.branch 29 (.branch 24 (.branch 21 (.leaf (12)) (.branch 22 (.leaf (13)) (.leaf (14)))) (.branch 26 (.leaf (15)) (.branch 27 (.leaf (16)) (.leaf (17))))) (.branch 34 (.branch 31 (.leaf (18)) (.branch 32 (.leaf (19)) (.leaf (20)))) (.branch 37 (.branch 36 (.leaf (21)) (.leaf (22))) (.branch 39 (.leaf (23)) (.leaf (24))))))),
  (.branch 20 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-27))),
  (.branch 33 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 38 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 19 (.branch 16 (.branch 14 (.leaf (-27)) (.branch 15 (.leaf (-26)) (.leaf (-25)))) (.branch 17 (.leaf (-24)) (.branch 18 (.leaf (-23)) (.leaf (-22))))) (.branch 22 (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19)))) (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))))) (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_044_656 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (0)))) (.branch 17 (.branch 16 (.leaf (4)) (.leaf (0))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (6))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (3)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (0))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_656
  counts := ![(.branch 19 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 10 (.leaf (5)) (.branch 12 (.leaf (6)) (.leaf (7)))) (.branch 15 (.leaf (8)) (.branch 17 (.leaf (9)) (.leaf (10)))))) (.branch 30 (.branch 24 (.branch 21 (.leaf (11)) (.branch 22 (.leaf (12)) (.leaf (13)))) (.branch 26 (.leaf (14)) (.branch 28 (.leaf (15)) (.leaf (16))))) (.branch 35 (.branch 32 (.leaf (17)) (.branch 34 (.leaf (18)) (.leaf (19)))) (.branch 37 (.leaf (20)) (.branch 39 (.leaf (21)) (.leaf (22))))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 22 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-33))),
  (.branch 27 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 36 (.branch 23 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.leaf (-8)))),
  (.branch 32 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-33)) (.leaf (-32))) (.branch 10 (.leaf (-31)) (.leaf (-30)))) (.branch 13 (.branch 12 (.leaf (-29)) (.leaf (-28))) (.branch 14 (.leaf (-27)) (.leaf (-26))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-25)) (.leaf (-24))) (.branch 18 (.leaf (-23)) (.leaf (-22)))) (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.leaf (-18)))))) (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_044_657 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (6)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (0)) (.leaf (2)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (5)) (.leaf (0))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (6)))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (4))) (.branch 33 (.leaf (0)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (5))))))))
  code := certificateD7_657
  counts := ![(.branch 18 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 15 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))))) (.branch 29 (.branch 22 (.branch 21 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14))))) (.branch 35 (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17)))) (.branch 37 (.leaf (18)) (.branch 38 (.leaf (19)) (.leaf (20))))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (-15)) (.leaf (-17)))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 37 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 24 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-17)) (.leaf (-15))) (.branch 35 (.leaf (-13)) (.leaf (-11)))) (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-7))) (.branch 39 (.leaf (-5)) (.leaf (-3))))),
  (.branch 13 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (0)))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_044_658 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (5)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (3)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (4)) (.branch 29 (.leaf (0)) (.leaf (6)))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (1))))))))
  code := certificateD7_658
  counts := ![(.branch 18 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 15 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))))) (.branch 29 (.branch 22 (.branch 21 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14))))) (.branch 35 (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17)))) (.branch 37 (.leaf (18)) (.branch 38 (.leaf (19)) (.leaf (20))))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 32 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-30))),
  (.branch 30 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 33 (.leaf (-3)) (.leaf (-2))) (.branch 35 (.leaf (-1)) (.leaf (0)))),
  (.branch 37 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 24 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.leaf (-30)) (.branch 12 (.leaf (-29)) (.leaf (-28)))) (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.leaf (-20)))) (.branch 23 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.leaf (-16)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_044_659 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (1)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (2))) (.branch 33 (.leaf (6)) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (1))))))))
  code := certificateD7_659
  counts := ![(.branch 18 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))) (.branch 29 (.branch 22 (.branch 21 (.leaf (9)) (.leaf (10))) (.branch 24 (.leaf (11)) (.branch 27 (.leaf (12)) (.leaf (13))))) (.branch 34 (.branch 31 (.leaf (14)) (.leaf (15))) (.branch 36 (.leaf (16)) (.branch 38 (.leaf (17)) (.leaf (18))))))),
  (.branch 20 (.branch 10 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-9)) (.leaf (-18)))) (.branch 22 (.leaf (-20)) (.branch 24 (.leaf (-22)) (.leaf (-24))))),
  (.leaf (0)),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 37 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-27))),
  (.branch 33 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 32 (.branch 25 (.leaf (-24)) (.leaf (-23))) (.branch 39 (.leaf (-22)) (.leaf (-15)))),
  (.leaf (0)),
  (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 19 (.branch 16 (.branch 14 (.leaf (-27)) (.branch 15 (.leaf (-26)) (.leaf (-25)))) (.branch 17 (.leaf (-24)) (.branch 18 (.leaf (-23)) (.leaf (-22))))) (.branch 22 (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19)))) (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))))) (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_044_660 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (1)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (2)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (6)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (4)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (3))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_660
  counts := ![(.branch 18 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 27 (.branch 22 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 25 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 30 (.leaf (12)) (.leaf (13))) (.branch 35 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 24 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))) (.branch 22 (.leaf (-17)) (.branch 27 (.leaf (-20)) (.leaf (-21))))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-29))),
  (.branch 31 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 36 (.branch 28 (.leaf (-21)) (.leaf (-20))) (.branch 39 (.leaf (-18)) (.leaf (-13)))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 38 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.branch 24 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 18 (.branch 14 (.branch 12 (.leaf (-29)) (.branch 13 (.leaf (-28)) (.leaf (-27)))) (.branch 16 (.branch 15 (.leaf (-26)) (.leaf (-25))) (.branch 17 (.leaf (-24)) (.leaf (-23))))) (.branch 21 (.branch 19 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20)))) (.branch 23 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.leaf (-16)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_044_661 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (5))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (6))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (1)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (2))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (6))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (2))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (1))))))))
  code := certificateD7_661
  counts := ![(.branch 18 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 22 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 25 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 30 (.leaf (12)) (.leaf (13))) (.branch 35 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 24 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 22 (.leaf (-22)) (.leaf (-26)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 31 (.leaf (-7)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-8)) (.leaf (-9)))),
  (.branch 26 (.leaf (0)) (.branch 39 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 12 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 36 (.branch 23 (.leaf (-26)) (.leaf (-25))) (.branch 39 (.leaf (-22)) (.leaf (-15)))),
  (.branch 37 (.branch 32 (.leaf (-12)) (.leaf (-9))) (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-1)) (.leaf (0))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.branch 20 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7)))) (.branch 38 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 39 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_044_662 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (5))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (0))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (6)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (4))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (2)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (0))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (3)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (6)) (.leaf (2))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (5)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (4))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_662
  counts := ![(.branch 18 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 27 (.branch 22 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 25 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 30 (.leaf (12)) (.leaf (13))) (.branch 35 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))) (.branch 22 (.leaf (-17)) (.branch 27 (.leaf (-20)) (.leaf (-21))))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 36 (.branch 28 (.leaf (-21)) (.leaf (-20))) (.branch 39 (.leaf (-18)) (.leaf (-13)))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 38 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.branch 24 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_044_663 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (5))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (6))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_663
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 23 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 24 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 27 (.leaf (10)) (.leaf (11)))) (.branch 34 (.branch 32 (.leaf (12)) (.leaf (13))) (.branch 37 (.leaf (14)) (.branch 39 (.leaf (15)) (.leaf (16))))))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-25))),
  (.branch 35 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 39 (.leaf (-4)) (.leaf (-2))),
  (.leaf (-2)),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 21 (.branch 18 (.branch 16 (.leaf (-25)) (.branch 17 (.leaf (-24)) (.leaf (-23)))) (.branch 19 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20))))) (.branch 24 (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17)))) (.branch 25 (.leaf (-16)) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_044_664 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (3)) (.branch 19 (.leaf (0)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (2)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (3)) (.branch 39 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_664
  counts := ![(.branch 19 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 15 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (10)) (.leaf (11))) (.branch 25 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14))))) (.branch 35 (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17)))) (.branch 37 (.leaf (18)) (.branch 39 (.leaf (19)) (.leaf (20))))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_044_665 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (2)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (6)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (2))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_665
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 23 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 17 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 22 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 24 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-30))),
  (.branch 30 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 39 (.leaf (-4)) (.leaf (-2))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0)),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.leaf (-30)) (.branch 12 (.leaf (-29)) (.leaf (-28)))) (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.leaf (-20)))) (.branch 23 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.leaf (-16)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_044_666 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (6))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (2)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (5))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_666
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 23 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 35 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-33))),
  (.branch 27 (.leaf (0)) (.leaf (-13))),
  (.branch 37 (.leaf (0)) (.leaf (-3))),
  (.branch 17 (.leaf (0)) (.leaf (-23)))]
  high := ![(.branch 39 (.leaf (-4)) (.leaf (-2))),
  (.branch 36 (.leaf (-5)) (.leaf (-3))),
  (.branch 35 (.leaf (-1)) (.leaf (0))),
  (.branch 23 (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-33)) (.leaf (-32))) (.branch 10 (.leaf (-31)) (.leaf (-30)))) (.branch 13 (.branch 12 (.leaf (-29)) (.leaf (-28))) (.branch 14 (.leaf (-27)) (.leaf (-26))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-25)) (.leaf (-24))) (.branch 18 (.leaf (-23)) (.leaf (-22)))) (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.leaf (-18)))))) (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 22 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_044_667 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (5))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (2)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (6))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_667
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 31 (.branch 25 (.branch 22 (.leaf (7)) (.leaf (8))) (.branch 28 (.leaf (9)) (.leaf (10)))) (.branch 36 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 39 (.leaf (13)) (.leaf (14)))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-6)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 17 (.leaf (0)) (.leaf (-23))),
  (.branch 37 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 30 (.branch 24 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 34 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7)))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 22 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_044_668 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (6)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (2)) (.leaf (4))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (5))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (3)) (.leaf (0))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (6)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_668
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 31 (.leaf (-17)) (.leaf (-19)))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 30 (.branch 24 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.leaf (-1)) (.leaf (0))),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-19)) (.leaf (-17))) (.branch 34 (.leaf (-15)) (.leaf (-13)))) (.branch 37 (.branch 36 (.leaf (-11)) (.leaf (-9))) (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 12 (.leaf (-5)) (.branch 26 (.leaf (-4)) (.leaf (-3)))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_044_669 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (5)) (.leaf (0))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (3)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (2)) (.leaf (3))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (4)) (.branch 29 (.leaf (2)) (.leaf (1)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (6)) (.leaf (0))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_669
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-8)))) (.branch 23 (.leaf (-9)) (.branch 33 (.leaf (-10)) (.leaf (-11))))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 16 (.leaf (0)) (.leaf (-24))),
  (.branch 36 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 38 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 39 (.leaf (-8)) (.leaf (-6)))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 22 (.branch 19 (.branch 17 (.leaf (-24)) (.branch 18 (.leaf (-23)) (.leaf (-22)))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_044_670 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (2)) (.leaf (4))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (4)) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (3))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_670
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 16 (.leaf (-4)) (.branch 36 (.leaf (-5)) (.leaf (-6))))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-6))) (.branch 33 (.leaf (-9)) (.leaf (-11)))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.leaf (0))]
  high := ![(.branch 30 (.branch 24 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 38 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 39 (.leaf (-4)) (.leaf (-3)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.branch 34 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-9)))) (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5))))),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_044_671 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (5))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (3)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (6))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_671
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 23 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 35 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 17 (.leaf (0)) (.leaf (-23))),
  (.branch 37 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 39 (.leaf (-4)) (.leaf (-2))),
  (.branch 36 (.leaf (-5)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 22 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_044_672 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (3)) (.branch 19 (.leaf (5)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (4))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (3)) (.branch 39 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_672
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 34 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 37 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 14 (.leaf (-3)) (.branch 34 (.leaf (-4)) (.leaf (-5))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 13 (.leaf (0)) (.branch 33 (.leaf (-1)) (.leaf (-2)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 30 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 19 (.leaf (0)) (.leaf (-21))),
  (.branch 39 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3)))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.leaf (-2)) (.branch 35 (.leaf (-1)) (.leaf (0)))),
  (.branch 31 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3)))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17))))) (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_044_673 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (3)) (.leaf (6))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (4)) (.leaf (0))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_673
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 16 (.leaf (-4)) (.branch 36 (.leaf (-5)) (.leaf (-6))))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (-3)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-35))),
  (.branch 25 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 30 (.branch 24 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 38 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 39 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-5)),
  (.branch 22 (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-35)) (.leaf (-34))) (.branch 8 (.leaf (-33)) (.leaf (-32)))) (.branch 11 (.branch 10 (.leaf (-31)) (.leaf (-30))) (.branch 12 (.leaf (-29)) (.leaf (-28))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))))) (.branch 31 (.branch 26 (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 28 (.branch 27 (.leaf (-14)) (.leaf (-13))) (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_044 : Fin 25 → CycleWitness 7 := ![witnessD7_044_649, witnessD7_044_650, witnessD7_044_651, witnessD7_044_652, witnessD7_044_653, witnessD7_044_654, witnessD7_044_655, witnessD7_044_656, witnessD7_044_657, witnessD7_044_658, witnessD7_044_659, witnessD7_044_660, witnessD7_044_661, witnessD7_044_662, witnessD7_044_663, witnessD7_044_664, witnessD7_044_665, witnessD7_044_666, witnessD7_044_667, witnessD7_044_668, witnessD7_044_669, witnessD7_044_670, witnessD7_044_671, witnessD7_044_672, witnessD7_044_673]
end RealPinwheel.FiveSixths


