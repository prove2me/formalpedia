-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_323
-- name    : RealPinwheel_FiveSixths_WitnessP9_323
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:38:11.966921+00:00
-- url     : https://prove2.me/theorems/769aa007-e58e-44e2-be8e-4996cb1bc239
-- title:
--   Exact witness block P9_323
-- statement:
--   These exact witnesses represent words 6775 through 6849 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 6775–6849; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_323_6774 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (7)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (3)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (8)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (3))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_6774
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 23 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 25 (.leaf (10)) (.leaf (11)))) (.branch 34 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 18 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-7)) (.leaf (-9)))) (.branch 25 (.branch 23 (.leaf (-10)) (.leaf (-11))) (.branch 38 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 39 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-31))),
  (.branch 19 (.leaf (0)) (.leaf (-21))),
  (.branch 29 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 39 (.leaf (-14)) (.leaf (-11))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.leaf (-2)) (.branch 34 (.leaf (-1)) (.leaf (0)))),
  (.branch 37 (.branch 25 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.leaf (-31)) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17))))) (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6775 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (4))) (.branch 12 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (7))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (1)) (.leaf (0)))))) (.branch 35 (.branch 31 (.branch 30 (.leaf (6)) (.leaf (3))) (.branch 32 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (4))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (8))))))))
  code := certificateP9_6775
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 14 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 8 (.leaf (-3)) (.leaf (-4)))) (.branch 28 (.branch 25 (.leaf (-6)) (.leaf (-7))) (.branch 34 (.leaf (-8)) (.leaf (-10))))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-28)) (.leaf (-29)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (-7))) (.branch 37 (.leaf (-8)) (.leaf (-9)))),
  (.branch 10 (.leaf (0)) (.leaf (-30))),
  (.branch 30 (.leaf (0)) (.leaf (-10))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.leaf (0))]
  high := ![(.branch 30 (.branch 24 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 35 (.leaf (-10)) (.leaf (-9))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.branch 32 (.branch 18 (.leaf (-29)) (.leaf (-27))) (.branch 33 (.leaf (-24)) (.branch 34 (.leaf (-21)) (.leaf (-18))))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.leaf (-30)) (.branch 12 (.leaf (-29)) (.leaf (-28)))) (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.leaf (-20)))) (.branch 23 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.leaf (-16)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_323_6776 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (6)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (7))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (4)) (.leaf (2))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (6)) (.branch 29 (.leaf (0)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (8))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (5))))))))
  code := certificateP9_6776
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-6))) (.branch 33 (.leaf (-9)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-19)) (.leaf (-22)))),
  (.branch 10 (.leaf (0)) (.branch 36 (.leaf (-7)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 17 (.leaf (0)) (.leaf (-23))),
  (.branch 37 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 30 (.branch 24 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 36 (.branch 34 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-9)))) (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5))))),
  (.branch 34 (.branch 31 (.branch 17 (.leaf (-22)) (.leaf (-21))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-17)) (.leaf (-15))))) (.branch 37 (.branch 35 (.leaf (-13)) (.branch 36 (.leaf (-11)) (.leaf (-9)))) (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-7))) (.branch 39 (.leaf (-5)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 22 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_323_6777 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (7))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (6))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (3)) (.leaf (2))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (5)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (2))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (8))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_6777
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 23 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 17 (.leaf (0)) (.leaf (-23))),
  (.branch 37 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 39 (.leaf (-4)) (.leaf (-2))),
  (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 28 (.branch 22 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_323_6778 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (7)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (3)) (.leaf (6))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (8)) (.leaf (0))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_6778
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 16 (.leaf (-4)) (.branch 36 (.leaf (-5)) (.leaf (-6))))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-35))),
  (.branch 25 (.leaf (0)) (.leaf (-15))),
  (.branch 11 (.leaf (0)) (.leaf (-29))),
  (.branch 31 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 30 (.branch 24 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 38 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 39 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-1)),
  (.branch 22 (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-35)) (.leaf (-34))) (.branch 8 (.leaf (-33)) (.leaf (-32)))) (.branch 11 (.branch 10 (.leaf (-31)) (.leaf (-30))) (.branch 12 (.leaf (-29)) (.leaf (-28))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))))) (.branch 31 (.branch 26 (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 28 (.branch 27 (.leaf (-14)) (.leaf (-13))) (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 18 (.branch 14 (.branch 12 (.leaf (-29)) (.branch 13 (.leaf (-28)) (.leaf (-27)))) (.branch 16 (.branch 15 (.leaf (-26)) (.leaf (-25))) (.branch 17 (.leaf (-24)) (.leaf (-23))))) (.branch 21 (.branch 19 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20)))) (.branch 23 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.leaf (-16)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6779 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (7)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (8))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (3)) (.leaf (6))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (5))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (7)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (4)) (.leaf (3))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (8))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6779
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 23 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (-19)) (.leaf (-20)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 17 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 39 (.leaf (-4)) (.leaf (-2))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 37 (.branch 25 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 21 (.leaf (-20)) (.branch 35 (.leaf (-18)) (.leaf (-15)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-9))) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_323_6780 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (7))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (6))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (4))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (6))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (3)) (.leaf (8))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (5))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (4)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (6)) (.leaf (3))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (4))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6780
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 23 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (-2))) (.branch 37 (.leaf (-5)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (-19)) (.leaf (-20)))),
  (.branch 5 (.leaf (0)) (.leaf (-35))),
  (.branch 25 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 39 (.leaf (-4)) (.leaf (-2))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 37 (.branch 25 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 36 (.branch 21 (.leaf (-20)) (.branch 35 (.leaf (-18)) (.leaf (-15)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-9))) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-35)) (.leaf (-34))) (.branch 8 (.leaf (-33)) (.leaf (-32)))) (.branch 11 (.branch 10 (.leaf (-31)) (.leaf (-30))) (.branch 12 (.leaf (-29)) (.leaf (-28))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))))) (.branch 31 (.branch 26 (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 28 (.branch 27 (.leaf (-14)) (.leaf (-13))) (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6781 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (7)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (4)) (.leaf (2))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (8)) (.leaf (0))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_6781
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-29))),
  (.branch 31 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 30 (.branch 24 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0)),
  (.branch 25 (.branch 18 (.branch 14 (.branch 12 (.leaf (-29)) (.branch 13 (.leaf (-28)) (.leaf (-27)))) (.branch 16 (.branch 15 (.leaf (-26)) (.leaf (-25))) (.branch 17 (.leaf (-24)) (.leaf (-23))))) (.branch 21 (.branch 19 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20)))) (.branch 23 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.leaf (-16)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6782 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (7)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (5)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (4)) (.leaf (3))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (6)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (8)) (.leaf (3))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_6782
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 23 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 14 (.leaf (0)) (.leaf (-26))),
  (.branch 34 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 39 (.leaf (-4)) (.leaf (-2))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 20 (.branch 17 (.branch 15 (.leaf (-26)) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 18 (.leaf (-23)) (.branch 19 (.leaf (-22)) (.leaf (-21))))) (.branch 23 (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18)))) (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6783 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (5)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (6)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (4)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (7))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (5)) (.leaf (2))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (6)) (.leaf (0))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_6783
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 11 (.leaf (0)) (.leaf (-9))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.leaf (0))]
  high := ![(.branch 30 (.branch 24 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_323_6784 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (5)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (7))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (5)) (.leaf (3))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (6))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (8))))))))
  code := certificateP9_6784
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 23 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-14)) (.leaf (-15)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.leaf (0))]
  high := ![(.branch 39 (.leaf (-4)) (.leaf (-2))),
  (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_323_6785 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (4)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (6))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (2))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (7)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (2))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_6785
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 22 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-30))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.branch 30 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 35 (.leaf (-8)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.leaf (-30)) (.branch 12 (.leaf (-29)) (.leaf (-28)))) (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.leaf (-20)))) (.branch 23 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.leaf (-16)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_323_6786 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (7)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (6))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (5)) (.leaf (0))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (3)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (2))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (8)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (6))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_6786
  counts := ![(.branch 19 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 24 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 27 (.leaf (9)) (.leaf (10)))) (.branch 36 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 39 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 35 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 8 (.leaf (-5)) (.branch 11 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-26))),
  (.branch 34 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 28 (.branch 22 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 34 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 37 (.leaf (-8)) (.leaf (-7))))),
  (.branch 32 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.branch 20 (.branch 17 (.branch 15 (.leaf (-26)) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 18 (.leaf (-23)) (.branch 19 (.leaf (-22)) (.leaf (-21))))) (.branch 23 (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18)))) (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6787 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (8)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (4)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (6))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (5)) (.leaf (2))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (7)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (6))))))))
  code := certificateP9_6787
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 22 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.leaf (0)),
  (.branch 30 (.leaf (0)) (.leaf (-10))),
  (.branch 10 (.leaf (0)) (.leaf (-30)))]
  high := ![(.branch 35 (.leaf (-8)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.leaf (-30)) (.branch 12 (.leaf (-29)) (.leaf (-28)))) (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.leaf (-20)))) (.branch 23 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.leaf (-16)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_323_6788 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (6))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (3))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (8)) (.branch 29 (.leaf (0)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (5))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (4))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (6))))))))
  code := certificateP9_6788
  counts := ![(.branch 19 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 24 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 34 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 39 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-32))),
  (.branch 28 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 37 (.leaf (-3)) (.leaf (-2))),
  (.branch 28 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-32)) (.leaf (-31))) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6789 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (5))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (1)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (7))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (1)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (3))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (6))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (1)) (.leaf (3))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (8))) (.branch 38 (.leaf (2)) (.branch 39 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_6789
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-33))),
  (.branch 27 (.leaf (0)) (.leaf (-13))),
  (.branch 17 (.leaf (0)) (.leaf (-23))),
  (.branch 37 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 23 (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-33)) (.leaf (-32))) (.branch 10 (.leaf (-31)) (.leaf (-30)))) (.branch 13 (.branch 12 (.leaf (-29)) (.leaf (-28))) (.branch 14 (.leaf (-27)) (.leaf (-26))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-25)) (.leaf (-24))) (.branch 18 (.leaf (-23)) (.leaf (-22)))) (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.leaf (-18)))))) (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 22 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_323_6790 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (0))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (6)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (8)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (4))))) (.branch 27 (.branch 26 (.leaf (6)) (.leaf (0))) (.branch 28 (.leaf (7)) (.branch 29 (.leaf (1)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (3)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (5)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (4))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (8)) (.leaf (6))))))))
  code := certificateP9_6790
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 24 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 27 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-13)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-17)) (.leaf (-20)))),
  (.branch 11 (.leaf (0)) (.branch 37 (.leaf (-5)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 26 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7)))),
  (.branch 37 (.branch 23 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 32 (.branch 18 (.leaf (-20)) (.leaf (-19))) (.branch 33 (.leaf (-17)) (.branch 34 (.leaf (-15)) (.leaf (-13))))) (.branch 37 (.branch 36 (.leaf (-11)) (.leaf (-9))) (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-5)) (.leaf (-3)))),
  (.branch 36 (.branch 21 (.branch 7 (.leaf (-15)) (.leaf (-14))) (.branch 35 (.leaf (-13)) (.leaf (-11)))) (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-7))) (.branch 39 (.leaf (-5)) (.leaf (-3))))),
  (.branch 27 (.leaf (-2)) (.leaf (0))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_323_6791 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (6))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (4)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (7))) (.branch 18 (.leaf (3)) (.branch 19 (.leaf (0)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (4))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (6))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (1)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (5)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (4)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (8))) (.branch 38 (.leaf (3)) (.branch 39 (.leaf (0)) (.leaf (5))))))))
  code := certificateP9_6791
  counts := ![(.branch 19 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 24 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 39 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 17 (.leaf (0)) (.leaf (-23))),
  (.branch 37 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 36 (.leaf (-4)) (.leaf (-3))),
  (.branch 37 (.branch 23 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 22 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_323_6792 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (2)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (6)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (4))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (8)) (.branch 29 (.leaf (2)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (5)) (.branch 34 (.leaf (0)) (.leaf (4))))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (6)) (.leaf (3))))))))
  code := certificateP9_6792
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-32))),
  (.branch 28 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 35 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-32)) (.leaf (-31))) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6793 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (1)) (.leaf (7))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (6)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (4))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (3))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (5)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (1)) (.leaf (8))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (6)) (.leaf (3))))))))
  code := certificateP9_6793
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-25))),
  (.branch 35 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 31 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 27 (.branch 21 (.branch 18 (.branch 16 (.leaf (-25)) (.branch 17 (.leaf (-24)) (.leaf (-23)))) (.branch 19 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20))))) (.branch 24 (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17)))) (.branch 25 (.leaf (-16)) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6794 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (7)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (4)) (.leaf (0))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (2)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (4))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (8)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (6))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (0))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (3)) (.leaf (5))))))))
  code := certificateP9_6794
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-31))),
  (.branch 29 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 27 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 37 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.leaf (-31)) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6795 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (8)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (6)) (.leaf (5))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (7))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (8)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (6)) (.leaf (4))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (5)) (.leaf (7))))))))
  code := certificateP9_6795
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 24 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 27 (.leaf (9)) (.leaf (10)))) (.branch 36 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-25))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (-4)) (.leaf (-5)))),
  (.branch 11 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 39 (.leaf (-14)) (.leaf (-7))),
  (.branch 37 (.branch 29 (.leaf (-16)) (.branch 36 (.leaf (-15)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 36 (.branch 24 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.branch 33 (.branch 6 (.leaf (-25)) (.leaf (-24))) (.branch 34 (.leaf (-21)) (.leaf (-18)))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 26 (.leaf (-5)) (.leaf (-3))),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6796 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (7))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (6)) (.branch 19 (.leaf (2)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (4))))) (.branch 27 (.branch 26 (.leaf (6)) (.leaf (2))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (5)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (3)) (.leaf (8))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (4))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (6)) (.branch 39 (.leaf (3)) (.leaf (5))))))))
  code := certificateP9_6796
  counts := ![(.branch 17 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 3 (.leaf (0)) (.branch 34 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (-5)) (.leaf (-7)))),
  (.branch 12 (.leaf (0)) (.leaf (-28))),
  (.branch 32 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 38 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 23 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 27 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))),
  (.branch 26 (.branch 19 (.branch 15 (.branch 13 (.leaf (-28)) (.branch 14 (.leaf (-27)) (.leaf (-26)))) (.branch 17 (.branch 16 (.leaf (-25)) (.leaf (-24))) (.branch 18 (.leaf (-23)) (.leaf (-22))))) (.branch 22 (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19)))) (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))))) (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6797 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (0)) (.leaf (8))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (6))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (0)) (.leaf (7))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_6797
  counts := ![(.branch 19 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 24 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 34 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 39 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (-19))) (.branch 33 (.leaf (-20)) (.leaf (-21)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-35))),
  (.branch 25 (.leaf (0)) (.leaf (-15))),
  (.branch 35 (.leaf (0)) (.leaf (-5))),
  (.branch 15 (.leaf (0)) (.leaf (-25)))]
  high := ![(.branch 37 (.leaf (-3)) (.leaf (-2))),
  (.branch 33 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 36 (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-18)) (.leaf (-15)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-9))) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 22 (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-35)) (.leaf (-34))) (.branch 8 (.leaf (-33)) (.leaf (-32)))) (.branch 11 (.branch 10 (.leaf (-31)) (.leaf (-30))) (.branch 12 (.leaf (-29)) (.leaf (-28))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))))) (.branch 31 (.branch 26 (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 28 (.branch 27 (.leaf (-14)) (.leaf (-13))) (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 21 (.branch 18 (.branch 16 (.leaf (-25)) (.branch 17 (.leaf (-24)) (.leaf (-23)))) (.branch 19 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20))))) (.branch 24 (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17)))) (.branch 25 (.leaf (-16)) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_323_6798 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (7))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (6)) (.leaf (0))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (2)) (.leaf (8))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (4)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (7))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (6)) (.leaf (0))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (3)) (.leaf (8))))))))
  code := certificateP9_6798
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 27 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessP9_323_6799 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (7)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (8)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (2)) (.leaf (3))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (6)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (3))))))))
  code := certificateP9_6799
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 24 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 27 (.leaf (9)) (.leaf (10)))) (.branch 36 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-4)) (.leaf (-5)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 32 (.leaf (-2)) (.leaf (-3)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-31))),
  (.branch 29 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 39 (.leaf (-14)) (.leaf (-7))),
  (.branch 37 (.branch 29 (.leaf (-16)) (.branch 36 (.leaf (-15)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3)))),
  (.branch 34 (.branch 33 (.leaf (-3)) (.leaf (-2))) (.branch 35 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.leaf (-31)) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6800 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (8)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (7)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 27 (.branch 26 (.leaf (8)) (.leaf (2))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (4)) (.leaf (1)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (6)) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (4))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (7)) (.leaf (3))))))))
  code := certificateP9_6800
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 35 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (-2))) (.branch 37 (.leaf (-5)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 35 (.leaf (-8)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 37 (.branch 36 (.leaf (-7)) (.leaf (-6))) (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3))))),
  (.branch 37 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6801 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (7))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (5))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (6))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (4)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (3)) (.leaf (8))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (5))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (4))))))))
  code := certificateP9_6801
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 24 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 27 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-13)) (.leaf (-15)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 26 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 12 (.leaf (0)) (.leaf (-28))),
  (.branch 32 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 36 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-7)))),
  (.branch 37 (.branch 29 (.leaf (-7)) (.leaf (-6))) (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 19 (.branch 15 (.branch 13 (.leaf (-28)) (.branch 14 (.leaf (-27)) (.leaf (-26)))) (.branch 17 (.branch 16 (.leaf (-25)) (.leaf (-24))) (.branch 18 (.leaf (-23)) (.leaf (-22))))) (.branch 22 (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19)))) (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))))) (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6802 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (8)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (4))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (5))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (7))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (6))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (8)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (5))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (7))))))))
  code := certificateP9_6802
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 24 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 27 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-13)) (.leaf (-15)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 26 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 36 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-7)))),
  (.branch 37 (.branch 29 (.leaf (-7)) (.leaf (-6))) (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6803 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (1)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (6)) (.branch 19 (.leaf (2)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (8)) (.branch 29 (.leaf (1)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (4))) (.branch 33 (.leaf (6)) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (5)) (.branch 39 (.leaf (3)) (.leaf (4))))))))
  code := certificateP9_6803
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 20 (.leaf (0)) (.leaf (-2))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (-1))) (.branch 38 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-9)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.leaf (-32))),
  (.branch 28 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 37 (.branch 23 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 37 (.branch 27 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 21 (.leaf (-2)) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 39 (.leaf (-4)) (.leaf (-3))),
  (.branch 36 (.branch 34 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.leaf (-7)))) (.branch 38 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 39 (.leaf (-4)) (.leaf (-3))))),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-32)) (.leaf (-31))) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6804 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (5))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (7)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (6))))) (.branch 27 (.branch 26 (.leaf (5)) (.leaf (0))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (3)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (2)) (.leaf (4))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (8)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (5))))))))
  code := certificateP9_6804
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 24 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 27 (.leaf (9)) (.leaf (10)))) (.branch 36 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-4)) (.leaf (-5)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (-15)) (.leaf (-17)))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 14 (.leaf (0)) (.leaf (-26))),
  (.branch 34 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 39 (.leaf (-14)) (.leaf (-7))),
  (.branch 37 (.branch 29 (.leaf (-16)) (.branch 36 (.leaf (-15)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-1)),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-17)) (.leaf (-15))) (.branch 35 (.leaf (-13)) (.leaf (-11)))) (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-7))) (.branch 39 (.leaf (-5)) (.leaf (-3))))),
  (.branch 13 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (0)))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 20 (.branch 17 (.branch 15 (.leaf (-26)) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 18 (.leaf (-23)) (.branch 19 (.leaf (-22)) (.leaf (-21))))) (.branch 23 (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18)))) (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6805 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (7))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (4))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (8)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (6)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (7))))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (0))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (5)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (2)) (.leaf (3))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (8)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (6)) (.leaf (4))))))))
  code := certificateP9_6805
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 24 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 27 (.leaf (9)) (.leaf (10)))) (.branch 36 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (-15)) (.leaf (-17)))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 14 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 39 (.leaf (-14)) (.leaf (-7))),
  (.branch 37 (.branch 29 (.leaf (-16)) (.branch 36 (.leaf (-15)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3)))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-17)) (.leaf (-15))) (.branch 35 (.leaf (-13)) (.leaf (-11)))) (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-7))) (.branch 39 (.leaf (-5)) (.leaf (-3))))),
  (.branch 13 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (0)))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6806 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (6)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (4)) (.branch 19 (.leaf (7)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (4))) (.branch 28 (.leaf (6)) (.branch 29 (.leaf (0)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (5)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (4)) (.branch 39 (.leaf (8)) (.leaf (5))))))))
  code := certificateP9_6806
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 35 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 19 (.leaf (0)) (.leaf (-21))),
  (.branch 39 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 36 (.leaf (-7)) (.leaf (-6))) (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17))))) (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_323_6807 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (6)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (1)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (7)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (8)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (2)) (.branch 39 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_6807
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-8)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-34))),
  (.branch 14 (.leaf (0)) (.leaf (-26))),
  (.branch 26 (.leaf (0)) (.leaf (-14))),
  (.branch 34 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 38 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 23 (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-34)) (.leaf (-33))) (.branch 9 (.leaf (-32)) (.leaf (-31)))) (.branch 12 (.branch 11 (.leaf (-30)) (.leaf (-29))) (.branch 13 (.leaf (-28)) (.leaf (-27))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-26)) (.leaf (-25))) (.branch 17 (.leaf (-24)) (.leaf (-23)))) (.branch 20 (.branch 19 (.leaf (-22)) (.leaf (-21))) (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18))))))) (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 27 (.branch 20 (.branch 17 (.branch 15 (.leaf (-26)) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 18 (.leaf (-23)) (.branch 19 (.leaf (-22)) (.leaf (-21))))) (.branch 23 (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18)))) (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6808 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (7)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (1)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (4)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (6)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (8)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (4))) (.branch 38 (.leaf (2)) (.branch 39 (.leaf (1)) (.leaf (5))))))))
  code := certificateP9_6808
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (-28))) (.branch 30 (.leaf (-29)) (.leaf (-30)))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 14 (.leaf (0)) (.leaf (-26))),
  (.branch 34 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-27))) (.branch 33 (.leaf (-24)) (.branch 34 (.leaf (-21)) (.leaf (-18))))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 38 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 20 (.branch 17 (.branch 15 (.leaf (-26)) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 18 (.leaf (-23)) (.branch 19 (.leaf (-22)) (.leaf (-21))))) (.branch 23 (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18)))) (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6809 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (8)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (2)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (4)) (.leaf (1))) (.branch 33 (.leaf (6)) (.branch 34 (.leaf (0)) (.leaf (3))))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (7)) (.leaf (4))))))))
  code := certificateP9_6809
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 21 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 39 (.leaf (0)) (.leaf (-1))),
  (.branch 19 (.leaf (0)) (.leaf (-21)))]
  high := ![(.branch 22 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17))))) (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_323_6810 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (7))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (4)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (1))) (.branch 28 (.leaf (6)) (.branch 29 (.leaf (2)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (3)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (8))))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_6810
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 8 (.leaf (0)) (.leaf (-32))),
  (.branch 28 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-25))),
  (.branch 35 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 26 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-32)) (.leaf (-31))) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 21 (.branch 18 (.branch 16 (.leaf (-25)) (.branch 17 (.leaf (-24)) (.leaf (-23)))) (.branch 19 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20))))) (.branch 24 (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17)))) (.branch 25 (.leaf (-16)) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6811 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (6))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (7)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (5)) (.branch 29 (.leaf (3)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (2)) (.leaf (6))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (8)) (.leaf (3))))))))
  code := certificateP9_6811
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-19))) (.branch 31 (.leaf (-22)) (.leaf (-23)))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.branch 19 (.leaf (0)) (.leaf (-21))),
  (.branch 39 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 37 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 32 (.leaf (-23)) (.leaf (-21))) (.branch 39 (.leaf (-14)) (.leaf (-7)))),
  (.branch 12 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (0)))),
  (.branch 37 (.branch 25 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17))))) (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_323_6812 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (4)) (.branch 19 (.leaf (2)) (.leaf (8))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (5)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (7)) (.branch 29 (.leaf (0)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (4)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (6)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (5)) (.branch 39 (.leaf (3)) (.leaf (8))))))))
  code := certificateP9_6812
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-28))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-7)) (.leaf (-8)))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 27 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 35 (.branch 32 (.branch 5 (.leaf (-28)) (.leaf (-27))) (.branch 33 (.leaf (-24)) (.branch 34 (.leaf (-21)) (.leaf (-18))))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 25 (.leaf (-8)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_323_6813 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (3))) (.branch 8 (.leaf (8)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (5))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (7)) (.branch 19 (.leaf (6)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (5)) (.leaf (2))) (.branch 28 (.leaf (8)) (.branch 29 (.leaf (1)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (3)) (.leaf (6))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (4)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (7)) (.branch 39 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_6813
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (-22))) (.branch 32 (.leaf (-23)) (.leaf (-24)))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 23 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.leaf (-4)) (.leaf (-3))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-21))) (.branch 35 (.leaf (-18)) (.leaf (-15)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-9))) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6814 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (6)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (7)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (5)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (4)) (.leaf (3))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (6)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (8)) (.leaf (3))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 39 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_6814
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 14 (.leaf (0)) (.leaf (-26))),
  (.branch 34 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 20 (.branch 17 (.branch 15 (.leaf (-26)) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 18 (.leaf (-23)) (.branch 19 (.leaf (-22)) (.leaf (-21))))) (.branch 23 (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18)))) (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6815 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (7))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (6))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (4)) (.branch 19 (.leaf (2)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (5)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (4))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (8))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (6))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (4)) (.branch 39 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_6815
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-28))),
  (.branch 32 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 28 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.branch 19 (.branch 15 (.branch 13 (.leaf (-28)) (.branch 14 (.leaf (-27)) (.leaf (-26)))) (.branch 17 (.branch 16 (.leaf (-25)) (.leaf (-24))) (.branch 18 (.leaf (-23)) (.leaf (-22))))) (.branch 22 (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19)))) (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))))) (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6816 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (7)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (6)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (5)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (8)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (6)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (4))))))))
  code := certificateP9_6816
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 35 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-13)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.leaf (-30))),
  (.branch 30 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 32 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.leaf (0)),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.leaf (-30)) (.branch 12 (.leaf (-29)) (.leaf (-28)))) (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.leaf (-20)))) (.branch 23 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.leaf (-16)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6817 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (6)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (7)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (5)) (.branch 19 (.leaf (2)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (6)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (4)) (.branch 29 (.leaf (0)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (5)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (8)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (6)) (.branch 39 (.leaf (3)) (.leaf (4))))))))
  code := certificateP9_6817
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-28))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-7)) (.leaf (-8)))),
  (.branch 14 (.leaf (0)) (.leaf (-26))),
  (.branch 34 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 27 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 31 (.branch 29 (.leaf (-5)) (.branch 30 (.leaf (-4)) (.leaf (-3)))) (.branch 32 (.leaf (-2)) (.branch 33 (.leaf (-1)) (.leaf (0))))),
  (.branch 35 (.branch 32 (.branch 5 (.leaf (-28)) (.leaf (-27))) (.branch 33 (.leaf (-24)) (.branch 34 (.leaf (-21)) (.leaf (-18))))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 25 (.leaf (-8)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 27 (.branch 20 (.branch 17 (.branch 15 (.leaf (-26)) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 18 (.leaf (-23)) (.branch 19 (.leaf (-22)) (.leaf (-21))))) (.branch 23 (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18)))) (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6818 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (6)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (7))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (5))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (8)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (6)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (4)) (.branch 29 (.leaf (3)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (2)) (.leaf (7))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (3)) (.leaf (5))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (8)) (.leaf (3))))))))
  code := certificateP9_6818
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-19))) (.branch 31 (.leaf (-22)) (.leaf (-23)))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 37 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 32 (.leaf (-23)) (.leaf (-21))) (.branch 39 (.leaf (-14)) (.leaf (-7)))),
  (.branch 12 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (0)))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessP9_323_6819 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (6)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (8)) (.leaf (1))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (7)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (6)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (8)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (4)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (3)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (5)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (7)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (3))))))))
  code := certificateP9_6819
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 34 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6820 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (6)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (3)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (4))) (.branch 18 (.leaf (7)) (.branch 19 (.leaf (2)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (6)) (.leaf (4))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (5)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (6))) (.branch 33 (.leaf (4)) (.branch 34 (.leaf (2)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (5))) (.branch 38 (.leaf (8)) (.branch 39 (.leaf (3)) (.leaf (4))))))))
  code := certificateP9_6820
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 32 (.leaf (-10)) (.leaf (-12)))),
  (.branch 18 (.leaf (0)) (.leaf (-22))),
  (.branch 38 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 29 (.leaf (-16)) (.branch 36 (.leaf (-15)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 38 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-9)))) (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5))))),
  (.branch 29 (.branch 23 (.branch 20 (.branch 19 (.leaf (-22)) (.leaf (-21))) (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18))))) (.branch 26 (.branch 24 (.leaf (-17)) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_323_6821 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (7)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (8)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (6))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (2)) (.leaf (3))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (7)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (5))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (2))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (8)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (6))) (.branch 38 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))))))
  code := certificateP9_6821
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-33))) (.branch 23 (.leaf (-38)) (.leaf (-39)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-26)) (.leaf (-29)))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 33 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 36 (.branch 24 (.leaf (-39)) (.branch 30 (.leaf (-37)) (.leaf (-35)))) (.branch 38 (.branch 37 (.leaf (-28)) (.leaf (-21))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 37 (.branch 14 (.leaf (-29)) (.leaf (-28))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 27 (.branch 4 (.leaf (-19)) (.leaf (-18))) (.branch 33 (.leaf (-16)) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 34 (.leaf (-9)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6822 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (8)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (5))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (2)) (.leaf (6))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (5)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (7)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (4))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (3)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (2)) (.leaf (1))) (.branch 33 (.leaf (5)) (.branch 34 (.leaf (3)) (.leaf (6))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (4)) (.leaf (3))))))))
  code := certificateP9_6822
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-19))) (.branch 31 (.leaf (-22)) (.leaf (-23)))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (-1)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-13)) (.leaf (-16)))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 24 (.leaf (0)) (.leaf (-16))),
  (.branch 4 (.leaf (0)) (.leaf (-36)))]
  high := ![(.branch 37 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 32 (.leaf (-23)) (.leaf (-21))) (.branch 39 (.leaf (-14)) (.leaf (-7)))),
  (.branch 12 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (0)))),
  (.leaf (-3)),
  (.branch 36 (.branch 34 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-13)) (.leaf (-11)))) (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-7))) (.branch 39 (.leaf (-5)) (.leaf (-3))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 13 (.branch 8 (.branch 6 (.branch 5 (.leaf (-36)) (.leaf (-35))) (.branch 7 (.leaf (-34)) (.leaf (-33)))) (.branch 10 (.branch 9 (.leaf (-32)) (.leaf (-31))) (.branch 11 (.leaf (-30)) (.branch 12 (.leaf (-29)) (.leaf (-28)))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))))) (.branch 31 (.branch 26 (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 28 (.branch 27 (.leaf (-14)) (.leaf (-13))) (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_323_6823 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (8)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (5)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (4)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (5)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (7)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (5)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (3)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (6)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_6823
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 24 (.leaf (0)) (.leaf (-16))),
  (.branch 4 (.leaf (0)) (.leaf (-36)))]
  high := ![(.branch 34 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 13 (.branch 8 (.branch 6 (.branch 5 (.leaf (-36)) (.leaf (-35))) (.branch 7 (.leaf (-34)) (.leaf (-33)))) (.branch 10 (.branch 9 (.leaf (-32)) (.leaf (-31))) (.branch 11 (.leaf (-30)) (.branch 12 (.leaf (-29)) (.leaf (-28)))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))))) (.branch 31 (.branch 26 (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 28 (.branch 27 (.leaf (-14)) (.leaf (-13))) (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_323_6824 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (8)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (5))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (7))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (5))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (4))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (6)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (8)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (7)) (.leaf (5))) (.branch 28 (.leaf (4)) (.branch 29 (.leaf (1)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (3)) (.leaf (6))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (5))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (4))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (7)) (.leaf (3))))))))
  code := certificateP9_6824
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (-4))) (.branch 35 (.leaf (-7)) (.leaf (-9)))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (-22))) (.branch 32 (.leaf (-23)) (.leaf (-24)))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 26 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 23 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 36 (.leaf (-9)) (.leaf (-8))) (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-21))) (.branch 35 (.leaf (-18)) (.leaf (-15)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-9))) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 13 (.leaf (-4)) (.leaf (-3))),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6825 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (7)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (5)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (4))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (1)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (8)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (6)) (.leaf (2))))))))
  code := certificateP9_6825
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 19 (.leaf (0)) (.leaf (-21))),
  (.branch 39 (.leaf (0)) (.leaf (-1))),
  (.branch 16 (.leaf (0)) (.leaf (-24))),
  (.branch 36 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 35 (.leaf (-8)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17))))) (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1)),
  (.branch 28 (.branch 22 (.branch 19 (.branch 17 (.leaf (-24)) (.branch 18 (.leaf (-23)) (.leaf (-22)))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_323_6826 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (8)) (.branch 19 (.leaf (3)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (4)) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (3))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (6)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (4)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (3))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (7)) (.branch 39 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_6826
  counts := ![(.branch 17 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 10 (.leaf (-14)) (.branch 30 (.leaf (-18)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-31))),
  (.branch 29 (.leaf (0)) (.leaf (-11))),
  (.branch 38 (.leaf (0)) (.leaf (-2))),
  (.branch 18 (.leaf (0)) (.leaf (-22)))]
  high := ![(.branch 38 (.branch 31 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-14)) (.leaf (-9)))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.branch 26 (.leaf (-3)) (.leaf (-2))) (.branch 35 (.leaf (-1)) (.leaf (0)))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.leaf (-31)) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 29 (.branch 23 (.branch 20 (.branch 19 (.leaf (-22)) (.leaf (-21))) (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18))))) (.branch 26 (.branch 24 (.leaf (-17)) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_323_6827 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (5))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (7))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (6)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (4)) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (5))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (3)) (.leaf (1)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (2))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (8))))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (6)) (.leaf (2))))))))
  code := certificateP9_6827
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (-2)) (.leaf (-3)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-31))) (.branch 29 (.leaf (-32)) (.leaf (-33)))),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-25))),
  (.branch 35 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 35 (.leaf (-8)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.branch 33 (.leaf (-3)) (.leaf (-2))) (.branch 35 (.leaf (-1)) (.leaf (0)))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-33)) (.leaf (-30))) (.branch 32 (.leaf (-27)) (.branch 33 (.leaf (-24)) (.leaf (-21))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-15)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 37 (.branch 10 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 27 (.branch 21 (.branch 18 (.branch 16 (.leaf (-25)) (.branch 17 (.leaf (-24)) (.leaf (-23)))) (.branch 19 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20))))) (.branch 24 (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17)))) (.branch 25 (.leaf (-16)) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6828 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (5))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (7)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (6)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (5))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (4)) (.leaf (1)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (8)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (6)) (.leaf (4))))))))
  code := certificateP9_6828
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 16 (.leaf (0)) (.leaf (-24))),
  (.branch 36 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 35 (.leaf (-8)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 28 (.branch 22 (.branch 19 (.branch 17 (.leaf (-24)) (.branch 18 (.leaf (-23)) (.leaf (-22)))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_323_6829 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (8))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (4)) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (5)) (.branch 29 (.leaf (1)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (6))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (3))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (2)) (.branch 39 (.leaf (4)) (.leaf (7))))))))
  code := certificateP9_6829
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 38 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 20 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 37 (.branch 23 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 39 (.leaf (-4)) (.leaf (-3))),
  (.branch 37 (.branch 27 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_323_6830 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (7)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (6))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 27 (.branch 26 (.leaf (5)) (.leaf (0))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (4)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (2)) (.leaf (3))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (8)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (6))) (.branch 38 (.leaf (2)) (.branch 39 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_6830
  counts := ![(.branch 19 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 24 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 27 (.leaf (9)) (.leaf (10)))) (.branch 36 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 39 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-26))),
  (.branch 34 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 28 (.branch 22 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 34 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 37 (.leaf (-8)) (.leaf (-7))))),
  (.branch 37 (.branch 29 (.leaf (-16)) (.branch 36 (.leaf (-15)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 32 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.branch 20 (.branch 17 (.branch 15 (.leaf (-26)) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 18 (.leaf (-23)) (.branch 19 (.leaf (-22)) (.leaf (-21))))) (.branch 23 (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18)))) (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6831 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (7))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (6)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (4)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (0))) (.branch 18 (.leaf (8)) (.branch 19 (.leaf (1)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (7))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (6)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (5)) (.leaf (3))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (8)) (.branch 39 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_6831
  counts := ![(.branch 17 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-26)) (.leaf (-29)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 33 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-8)) (.leaf (-10)))),
  (.branch 26 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 38 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 14 (.leaf (-29)) (.leaf (-28))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 34 (.leaf (-9)) (.leaf (-7))),
  (.branch 37 (.branch 24 (.leaf (-10)) (.branch 36 (.leaf (-9)) (.leaf (-8)))) (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5))))),
  (.branch 27 (.leaf (-2)) (.leaf (0))),
  (.branch 36 (.branch 21 (.branch 7 (.leaf (-15)) (.leaf (-14))) (.branch 35 (.leaf (-13)) (.leaf (-11)))) (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-7))) (.branch 39 (.leaf (-5)) (.leaf (-3))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_323_6832 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (7)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (1))) (.branch 18 (.leaf (4)) (.branch 19 (.leaf (0)) (.leaf (6))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (8)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (4)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (1))) (.branch 38 (.leaf (5)) (.branch 39 (.leaf (0)) (.leaf (6))))))))
  code := certificateP9_6832
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 24 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 28 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 39 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 35 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (-25))) (.branch 31 (.leaf (-26)) (.leaf (-27)))),
  (.branch 11 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-31))),
  (.branch 29 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 36 (.leaf (-4)) (.leaf (-3))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.branch 24 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-27)) (.leaf (-24))) (.branch 34 (.leaf (-21)) (.leaf (-18)))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 12 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.leaf (-31)) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6833 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (6))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (4)) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (8)) (.branch 29 (.leaf (0)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (2))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (6))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (4))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (2))))))))
  code := certificateP9_6833
  counts := ![(.branch 19 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 24 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 34 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 39 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 20 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-31))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-32))),
  (.branch 28 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 37 (.leaf (-3)) (.leaf (-2))),
  (.branch 28 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.leaf (-2)) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 34 (.branch 31 (.branch 4 (.leaf (-31)) (.leaf (-30))) (.branch 32 (.leaf (-27)) (.branch 33 (.leaf (-24)) (.leaf (-21))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-15)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 38 (.branch 24 (.leaf (-11)) (.leaf (-9))) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-32)) (.leaf (-31))) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6834 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (7))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (4)) (.branch 24 (.leaf (0)) (.leaf (6))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (2))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (3)) (.leaf (1)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (5))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (8))))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_6834
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (-4)) (.leaf (-6)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-31))) (.branch 29 (.leaf (-32)) (.leaf (-33)))),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.branch 32 (.leaf (-9)) (.leaf (-10)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (-2)) (.leaf (-3)))),
  (.branch 15 (.leaf (0)) (.leaf (-25))),
  (.branch 35 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 35 (.leaf (-8)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.leaf (-6)) (.leaf (-5))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-33)) (.leaf (-30))) (.branch 32 (.leaf (-27)) (.branch 33 (.leaf (-24)) (.leaf (-21))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-15)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 37 (.branch 10 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.leaf (-7)))) (.branch 38 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 39 (.leaf (-4)) (.leaf (-3))))),
  (.branch 27 (.branch 26 (.leaf (-3)) (.leaf (-2))) (.branch 28 (.leaf (-1)) (.leaf (0)))),
  (.branch 27 (.branch 21 (.branch 18 (.branch 16 (.leaf (-25)) (.branch 17 (.leaf (-24)) (.leaf (-23)))) (.branch 19 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20))))) (.branch 24 (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17)))) (.branch 25 (.leaf (-16)) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6835 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (7))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (1)) (.leaf (8))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (6)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (4)) (.branch 24 (.leaf (0)) (.leaf (7))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (2))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (5)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (1)) (.leaf (8))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (4))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (6)) (.leaf (2))))))))
  code := certificateP9_6835
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-31))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (-10)) (.leaf (-11)))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.leaf (-1)) (.leaf (0))),
  (.branch 34 (.branch 31 (.branch 4 (.leaf (-31)) (.leaf (-30))) (.branch 32 (.leaf (-27)) (.branch 33 (.leaf (-24)) (.leaf (-21))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-15)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 38 (.branch 24 (.leaf (-11)) (.leaf (-9))) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6836 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (7))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (4)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (8)) (.branch 24 (.leaf (2)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (3))) (.branch 28 (.leaf (5)) (.branch 29 (.leaf (0)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (2)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (6))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (2)) (.branch 39 (.leaf (4)) (.leaf (5))))))))
  code := certificateP9_6836
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 27 (.leaf (-8)) (.branch 34 (.leaf (-9)) (.leaf (-11))))),
  (.branch 8 (.leaf (0)) (.branch 39 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-33))),
  (.branch 23 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 37 (.branch 35 (.leaf (-11)) (.branch 36 (.leaf (-10)) (.leaf (-9)))) (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6))))),
  (.leaf (-6)),
  (.leaf (0)),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-33)) (.leaf (-32))) (.branch 10 (.leaf (-31)) (.leaf (-30)))) (.branch 13 (.branch 12 (.leaf (-29)) (.leaf (-28))) (.branch 14 (.leaf (-27)) (.leaf (-26))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-25)) (.leaf (-24))) (.branch 18 (.leaf (-23)) (.leaf (-22)))) (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.leaf (-18)))))) (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_323_6837 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (8))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (6))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (5)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (8)) (.branch 24 (.leaf (2)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (3))) (.branch 28 (.leaf (4)) (.branch 29 (.leaf (0)) (.leaf (7)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (2)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (6))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (2)) (.branch 39 (.leaf (5)) (.leaf (4))))))))
  code := certificateP9_6837
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 27 (.leaf (-8)) (.branch 34 (.leaf (-9)) (.leaf (-11))))),
  (.leaf (0)),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (-16)) (.leaf (-23))))]
  high := ![(.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 37 (.branch 35 (.leaf (-11)) (.branch 36 (.leaf (-10)) (.leaf (-9)))) (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6))))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 31 (.branch 9 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 37 (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-23)) (.leaf (-22))) (.branch 26 (.leaf (-21)) (.leaf (-20)))) (.branch 29 (.branch 28 (.leaf (-19)) (.leaf (-18))) (.branch 30 (.leaf (-17)) (.leaf (-16))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-15)) (.leaf (-14))) (.branch 34 (.leaf (-13)) (.leaf (-12)))) (.branch 37 (.branch 36 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-8)) (.leaf (-7)))))))]
def witnessP9_323_6838 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (1))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (6)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (4)) (.branch 19 (.leaf (1)) (.leaf (7))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (2)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (5)) (.leaf (1))) (.branch 28 (.leaf (4)) (.branch 29 (.leaf (0)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (6)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (4)) (.branch 39 (.leaf (1)) (.leaf (8))))))))
  code := certificateP9_6838
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.leaf (0))]
  high := ![(.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 38 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_323_6839 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (7)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (4))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (6))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (2)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (8)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (4))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (5))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (3))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_6839
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 35 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 20 (.leaf (0)) (.leaf (-2))),
  (.branch 35 (.leaf (0)) (.leaf (-5))),
  (.branch 15 (.leaf (0)) (.leaf (-25))),
  (.branch 6 (.leaf (0)) (.leaf (-34))),
  (.branch 26 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 34 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 31 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 21 (.leaf (-2)) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 21 (.branch 18 (.branch 16 (.leaf (-25)) (.branch 17 (.leaf (-24)) (.leaf (-23)))) (.branch 19 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20))))) (.branch 24 (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17)))) (.branch 25 (.leaf (-16)) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-34)) (.leaf (-33))) (.branch 9 (.leaf (-32)) (.leaf (-31)))) (.branch 12 (.branch 11 (.leaf (-30)) (.leaf (-29))) (.branch 13 (.leaf (-28)) (.leaf (-27))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-26)) (.leaf (-25))) (.branch 17 (.leaf (-24)) (.leaf (-23)))) (.branch 20 (.branch 19 (.leaf (-22)) (.leaf (-21))) (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18))))))) (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6840 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (7)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (5))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (6))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (2)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (8)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (5))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (4))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (3))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_6840
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-34))),
  (.branch 26 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 34 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 31 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 23 (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-34)) (.leaf (-33))) (.branch 9 (.leaf (-32)) (.leaf (-31)))) (.branch 12 (.branch 11 (.leaf (-30)) (.leaf (-29))) (.branch 13 (.leaf (-28)) (.leaf (-27))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-26)) (.leaf (-25))) (.branch 17 (.leaf (-24)) (.leaf (-23)))) (.branch 20 (.branch 19 (.leaf (-22)) (.leaf (-21))) (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18))))))) (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6841 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (6)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (7)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (5)) (.leaf (6))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (2)) (.leaf (4))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (8)) (.leaf (4))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (5)) (.leaf (6))))))))
  code := certificateP9_6841
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-26))),
  (.branch 34 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 20 (.branch 17 (.branch 15 (.leaf (-26)) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 18 (.leaf (-23)) (.branch 19 (.leaf (-22)) (.leaf (-21))))) (.branch 23 (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18)))) (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6842 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (7))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (4)) (.leaf (0))) (.branch 18 (.leaf (8)) (.branch 19 (.leaf (1)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (5)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (7))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (3))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (6)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (5)) (.leaf (0))) (.branch 38 (.leaf (8)) (.branch 39 (.leaf (1)) (.leaf (2))))))))
  code := certificateP9_6842
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-19)) (.leaf (-22)))),
  (.branch 10 (.leaf (0)) (.branch 36 (.leaf (-7)) (.leaf (-9)))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 38 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 31 (.branch 17 (.leaf (-22)) (.leaf (-21))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-17)) (.leaf (-15))))) (.branch 37 (.branch 35 (.leaf (-13)) (.branch 36 (.leaf (-11)) (.leaf (-9)))) (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-7))) (.branch 39 (.leaf (-5)) (.leaf (-3)))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_323_6843 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (6))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (7))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (6))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (1)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (5)) (.leaf (2))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (4)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (8))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6843
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-14)) (.leaf (-15)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 28 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 17 (.leaf (0)) (.leaf (-23))),
  (.branch 37 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 34 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 33 (.leaf (-4)) (.leaf (-3))),
  (.branch 37 (.branch 29 (.leaf (-7)) (.leaf (-6))) (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 22 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_323_6844 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (4)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (7))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (5))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (6))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (8))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (3)) (.leaf (5))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (4))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (3))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_6844
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-26))) (.branch 30 (.leaf (-29)) (.leaf (-30)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-33))),
  (.branch 27 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 30 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 31 (.leaf (-30)) (.leaf (-28))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 11 (.leaf (-10)) (.branch 34 (.leaf (-9)) (.leaf (-7)))),
  (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3)))),
  (.branch 37 (.branch 25 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 23 (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-33)) (.leaf (-32))) (.branch 10 (.leaf (-31)) (.leaf (-30)))) (.branch 13 (.branch 12 (.leaf (-29)) (.leaf (-28))) (.branch 14 (.leaf (-27)) (.leaf (-26))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-25)) (.leaf (-24))) (.branch 18 (.leaf (-23)) (.leaf (-22)))) (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.leaf (-18)))))) (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6845 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (6))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (7))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (5)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (6)) (.branch 19 (.leaf (4)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (5)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (6))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (4)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (8))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (5)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (6)) (.branch 39 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_6845
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.leaf (0)) (.leaf (-28))),
  (.branch 32 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 37 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 37 (.branch 29 (.leaf (-16)) (.branch 36 (.leaf (-15)) (.leaf (-12)))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 27 (.leaf (-2)) (.branch 34 (.leaf (-1)) (.leaf (0)))),
  (.branch 31 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-1)),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 26 (.branch 19 (.branch 15 (.branch 13 (.leaf (-28)) (.branch 14 (.leaf (-27)) (.leaf (-26)))) (.branch 17 (.branch 16 (.leaf (-25)) (.leaf (-24))) (.branch 18 (.leaf (-23)) (.leaf (-22))))) (.branch 22 (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19)))) (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))))) (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_323_6846 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (8)) (.leaf (0))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (6)) (.leaf (1))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (7))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (5))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (6)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (8)) (.leaf (0))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (4)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (5)) (.leaf (1))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (0)) (.leaf (7))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (6))) (.branch 38 (.leaf (2)) (.branch 39 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_6846
  counts := ![(.branch 19 (.branch 7 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 25 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 27 (.leaf (9)) (.leaf (10)))) (.branch 36 (.branch 34 (.leaf (11)) (.leaf (12))) (.branch 39 (.leaf (13)) (.leaf (14)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-28)) (.leaf (-29)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (-7))) (.branch 37 (.leaf (-8)) (.leaf (-9)))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-14)))]
  high := ![(.leaf (-3)),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 35 (.branch 32 (.branch 18 (.leaf (-29)) (.leaf (-27))) (.branch 33 (.leaf (-24)) (.branch 34 (.leaf (-21)) (.leaf (-18))))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_323_6847 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (5)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (6)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (4)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (5))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (2)) (.leaf (7))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (3))) (.branch 23 (.leaf (4)) (.branch 24 (.leaf (1)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (3))) (.branch 28 (.leaf (6)) (.branch 29 (.leaf (0)) (.leaf (1)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (5)) (.leaf (4))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (3))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (8)) (.branch 39 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_6847
  counts := ![(.branch 21 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 25 (.leaf (5)) (.leaf (6))) (.branch 34 (.leaf (7)) (.branch 37 (.leaf (8)) (.leaf (9)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 29 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 37 (.leaf (-17)) (.leaf (-23)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-15))) (.branch 18 (.leaf (-18)) (.leaf (-20)))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))) (.branch 22 (.leaf (-15)) (.branch 27 (.leaf (-16)) (.leaf (-21))))),
  (.branch 8 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-28)) (.leaf (-29)))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (-11)) (.leaf (-12)))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.branch 38 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-19)) (.leaf (-15)))),
  (.branch 31 (.branch 19 (.leaf (-20)) (.branch 25 (.leaf (-19)) (.leaf (-18)))) (.branch 38 (.branch 37 (.leaf (-17)) (.leaf (-13))) (.branch 39 (.leaf (-9)) (.leaf (-5))))),
  (.branch 6 (.leaf (-7)) (.leaf (-6))),
  (.branch 37 (.branch 28 (.leaf (-21)) (.branch 36 (.leaf (-20)) (.leaf (-18)))) (.branch 38 (.leaf (-16)) (.branch 39 (.leaf (-14)) (.leaf (-12))))),
  (.branch 24 (.branch 15 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.branch 34 (.leaf (-2)) (.leaf (0))))),
  (.branch 35 (.branch 32 (.branch 18 (.leaf (-29)) (.leaf (-27))) (.branch 33 (.leaf (-24)) (.branch 34 (.leaf (-21)) (.leaf (-18))))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_323_6848 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (5)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (6)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (2))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (4)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (7))) (.branch 18 (.leaf (3)) (.branch 19 (.leaf (2)) (.leaf (6))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (4)) (.branch 24 (.leaf (5)) (.leaf (2))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (6)) (.branch 29 (.leaf (1)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (4)) (.leaf (2))) (.branch 33 (.leaf (5)) (.branch 34 (.leaf (3)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (8))) (.branch 38 (.leaf (4)) (.branch 39 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_6848
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-5)))),
  (.branch 17 (.leaf (0)) (.leaf (-23))),
  (.branch 37 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 37 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 29 (.leaf (-5)) (.branch 30 (.leaf (-4)) (.leaf (-3)))) (.branch 32 (.leaf (-2)) (.branch 33 (.leaf (-1)) (.leaf (0))))),
  (.branch 28 (.branch 22 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_323 : Fin 75 → CycleWitness 9 := ![witnessP9_323_6774, witnessP9_323_6775, witnessP9_323_6776, witnessP9_323_6777, witnessP9_323_6778, witnessP9_323_6779, witnessP9_323_6780, witnessP9_323_6781, witnessP9_323_6782, witnessP9_323_6783, witnessP9_323_6784, witnessP9_323_6785, witnessP9_323_6786, witnessP9_323_6787, witnessP9_323_6788, witnessP9_323_6789, witnessP9_323_6790, witnessP9_323_6791, witnessP9_323_6792, witnessP9_323_6793, witnessP9_323_6794, witnessP9_323_6795, witnessP9_323_6796, witnessP9_323_6797, witnessP9_323_6798, witnessP9_323_6799, witnessP9_323_6800, witnessP9_323_6801, witnessP9_323_6802, witnessP9_323_6803, witnessP9_323_6804, witnessP9_323_6805, witnessP9_323_6806, witnessP9_323_6807, witnessP9_323_6808, witnessP9_323_6809, witnessP9_323_6810, witnessP9_323_6811, witnessP9_323_6812, witnessP9_323_6813, witnessP9_323_6814, witnessP9_323_6815, witnessP9_323_6816, witnessP9_323_6817, witnessP9_323_6818, witnessP9_323_6819, witnessP9_323_6820, witnessP9_323_6821, witnessP9_323_6822, witnessP9_323_6823, witnessP9_323_6824, witnessP9_323_6825, witnessP9_323_6826, witnessP9_323_6827, witnessP9_323_6828, witnessP9_323_6829, witnessP9_323_6830, witnessP9_323_6831, witnessP9_323_6832, witnessP9_323_6833, witnessP9_323_6834, witnessP9_323_6835, witnessP9_323_6836, witnessP9_323_6837, witnessP9_323_6838, witnessP9_323_6839, witnessP9_323_6840, witnessP9_323_6841, witnessP9_323_6842, witnessP9_323_6843, witnessP9_323_6844, witnessP9_323_6845, witnessP9_323_6846, witnessP9_323_6847, witnessP9_323_6848]
end RealPinwheel.FiveSixths


