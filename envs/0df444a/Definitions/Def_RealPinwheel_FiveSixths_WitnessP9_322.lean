-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_322
-- name    : RealPinwheel_FiveSixths_WitnessP9_322
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:37:11.1792+00:00
-- url     : https://prove2.me/theorems/1f015b33-286a-41cb-ac29-822bfd62908d
-- title:
--   Exact witness block P9_322
-- statement:
--   These exact witnesses represent words 6703 through 6774 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 6703–6774; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_322_6702 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (0)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (6)) (.branch 20 (.leaf (3)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (1))) (.branch 29 (.leaf (8)) (.branch 30 (.leaf (0)) (.leaf (4)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (5)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (3)) (.leaf (2))))))))
  code := certificateP9_6702
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-13)) (.leaf (-14)))) (.branch 17 (.leaf (-15)) (.branch 38 (.leaf (-17)) (.leaf (-18))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 12 (.leaf (-14)) (.leaf (-15)))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 25 (.leaf (-3)) (.branch 36 (.leaf (-5)) (.leaf (-6))))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 10 (.leaf (0)) (.branch 37 (.leaf (-4)) (.leaf (-5)))),
  (.branch 19 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-34))),
  (.branch 29 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-14))) (.branch 41 (.leaf (-10)) (.leaf (-6)))),
  (.branch 40 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 36 (.branch 33 (.branch 17 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-34)) (.leaf (-33))) (.branch 11 (.leaf (-32)) (.leaf (-31)))) (.branch 14 (.branch 13 (.leaf (-30)) (.leaf (-29))) (.branch 15 (.leaf (-28)) (.leaf (-27))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-26)) (.leaf (-25))) (.branch 19 (.leaf (-24)) (.leaf (-23)))) (.branch 22 (.branch 21 (.leaf (-22)) (.leaf (-21))) (.branch 23 (.leaf (-20)) (.branch 24 (.leaf (-19)) (.leaf (-18))))))) (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 35 (.branch 32 (.branch 30 (.leaf (-13)) (.branch 31 (.leaf (-12)) (.leaf (-11)))) (.branch 33 (.leaf (-10)) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6703 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (1))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (4))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (8)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (1)) (.leaf (5))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (1))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (2)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (4))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (0)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (7)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (1)) (.leaf (6))))))))
  code := certificateP9_6703
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.branch 23 (.leaf (-9)) (.leaf (-10)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 30 (.leaf (-12)) (.leaf (-15)))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 33 (.leaf (-10)) (.leaf (-11)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 37 (.leaf (0)) (.leaf (-5))),
  (.branch 16 (.leaf (0)) (.leaf (-26)))]
  high := ![(.branch 40 (.branch 27 (.leaf (-17)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 24 (.leaf (-10)) (.branch 37 (.leaf (-9)) (.leaf (-6)))),
  (.branch 39 (.branch 31 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-10)) (.leaf (-8))))),
  (.branch 30 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.leaf (-8)))) (.branch 39 (.branch 38 (.leaf (-7)) (.leaf (-6))) (.branch 40 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 22 (.branch 19 (.branch 17 (.leaf (-26)) (.branch 18 (.leaf (-25)) (.leaf (-24)))) (.branch 20 (.leaf (-23)) (.branch 21 (.leaf (-22)) (.leaf (-21))))) (.branch 25 (.branch 23 (.leaf (-20)) (.branch 24 (.leaf (-19)) (.leaf (-18)))) (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))))) (.branch 35 (.branch 32 (.branch 30 (.leaf (-13)) (.branch 31 (.leaf (-12)) (.leaf (-11)))) (.branch 33 (.leaf (-10)) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_322_6704 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (6)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (7)) (.branch 20 (.leaf (2)) (.leaf (6))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (6)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (0)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (5)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (8)) (.branch 41 (.leaf (3)) (.leaf (6))))))))
  code := certificateP9_6704
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 35 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 41 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-9)))) (.branch 32 (.branch 14 (.leaf (-11)) (.leaf (-13))) (.branch 35 (.leaf (-14)) (.leaf (-16))))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))) (.branch 28 (.leaf (-7)) (.branch 36 (.leaf (-8)) (.leaf (-9))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (-2))) (.branch 41 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-15)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-10)))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 19 (.leaf (0)) (.leaf (-23))),
  (.branch 40 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 40 (.branch 36 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-12)) (.leaf (-9)))),
  (.branch 39 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7)))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4))))),
  (.leaf (-4)),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-14))) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 39 (.branch 38 (.leaf (-10)) (.leaf (-8))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 30 (.branch 24 (.branch 21 (.branch 20 (.leaf (-23)) (.leaf (-22))) (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19))))) (.branch 27 (.branch 25 (.leaf (-18)) (.branch 26 (.leaf (-17)) (.leaf (-16)))) (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))))) (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_322_6705 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (6))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (7))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (5))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 19 (.leaf (6)) (.branch 20 (.leaf (4)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (6))) (.branch 29 (.leaf (1)) (.branch 30 (.leaf (2)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (5)) (.leaf (8))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_6705
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 41 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-22))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 27 (.leaf (-12)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.branch 28 (.leaf (-4)) (.leaf (-5)))),
  (.branch 12 (.leaf (0)) (.leaf (-30))),
  (.branch 33 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 40 (.branch 27 (.leaf (-17)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 39 (.branch 30 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 5 (.leaf (-22)) (.branch 22 (.leaf (-21)) (.leaf (-20)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 38 (.branch 28 (.leaf (-14)) (.branch 37 (.leaf (-13)) (.leaf (-11)))) (.branch 40 (.branch 39 (.leaf (-9)) (.leaf (-7))) (.branch 41 (.leaf (-5)) (.leaf (-3))))),
  (.branch 7 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 29 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-3)))),
  (.branch 27 (.branch 19 (.branch 15 (.branch 13 (.leaf (-30)) (.branch 14 (.leaf (-29)) (.leaf (-28)))) (.branch 17 (.branch 16 (.leaf (-27)) (.leaf (-26))) (.branch 18 (.leaf (-25)) (.leaf (-24))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-23)) (.leaf (-22))) (.branch 22 (.leaf (-21)) (.leaf (-20)))) (.branch 25 (.branch 24 (.leaf (-19)) (.leaf (-18))) (.branch 26 (.leaf (-17)) (.leaf (-16)))))) (.branch 34 (.branch 30 (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6706 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (2)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (7))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (3)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (1)))) (.branch 19 (.leaf (8)) (.branch 20 (.leaf (2)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (2)) (.leaf (6))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (1)) (.branch 30 (.leaf (2)) (.leaf (4)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (7))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (3)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (1)))) (.branch 40 (.leaf (8)) (.branch 41 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_6706
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 11 (.leaf (-18)) (.branch 16 (.leaf (-19)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-16))),
  (.branch 12 (.leaf (0)) (.leaf (-9))),
  (.branch 19 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 39 (.branch 38 (.leaf (-20)) (.leaf (-16))) (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-8)) (.leaf (-4))))),
  (.branch 40 (.branch 24 (.leaf (-13)) (.leaf (-12))) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.branch 31 (.leaf (-6)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_322_6707 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (2)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (7)) (.leaf (3))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (6)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (4)) (.leaf (5))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (1)) (.leaf (6))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (5)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (3)) (.leaf (0))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (8)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (6)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (5))))))))
  code := certificateP9_6707
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 41 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-17)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-9)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-27))) (.branch 36 (.leaf (-29)) (.leaf (-30)))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-7)) (.leaf (-10)))),
  (.branch 14 (.leaf (0)) (.leaf (-28))),
  (.branch 35 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 39 (.branch 28 (.leaf (-18)) (.leaf (-16))) (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-8)) (.leaf (-4))))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-5)))),
  (.branch 39 (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-25)) (.leaf (-20)))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.branch 32 (.branch 31 (.leaf (-3)) (.leaf (-2))) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 40 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.leaf (-7)))),
  (.branch 28 (.branch 21 (.branch 17 (.branch 15 (.leaf (-28)) (.branch 16 (.leaf (-27)) (.leaf (-26)))) (.branch 19 (.branch 18 (.leaf (-25)) (.leaf (-24))) (.branch 20 (.leaf (-23)) (.leaf (-22))))) (.branch 24 (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19)))) (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))))) (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_322_6708 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (5))))) (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (3)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (7)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (2))) (.branch 29 (.leaf (1)) (.branch 30 (.leaf (0)) (.leaf (4)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (3)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (5))))) (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (0)) (.leaf (3)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (8)) (.leaf (2))))))))
  code := certificateP9_6708
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-16)) (.leaf (-17)))) (.branch 13 (.leaf (-18)) (.branch 17 (.leaf (-19)) (.leaf (-20))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 23 (.leaf (-6)) (.branch 33 (.leaf (-7)) (.leaf (-9))))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 15 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 20 (.leaf (0)) (.leaf (-22))),
  (.branch 41 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 40 (.branch 39 (.leaf (-20)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 30 (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 25 (.branch 22 (.branch 21 (.leaf (-22)) (.leaf (-21))) (.branch 23 (.leaf (-20)) (.branch 24 (.leaf (-19)) (.leaf (-18))))) (.branch 28 (.branch 26 (.leaf (-17)) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_322_6709 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (5))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (7)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (1)) (.leaf (5))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (6)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (4)) (.leaf (0))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (1))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (4))) (.branch 29 (.leaf (1)) (.branch 30 (.leaf (3)) (.leaf (8)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (5))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (1)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (6)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_6709
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 41 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 26 (.leaf (-17)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 23 (.leaf (-7)) (.leaf (-9)))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 28 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 36 (.leaf (-12)) (.leaf (-13)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.branch 27 (.leaf (-5)) (.leaf (-6)))),
  (.branch 10 (.leaf (0)) (.leaf (-32))),
  (.branch 31 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 39 (.branch 27 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-14)))) (.branch 40 (.leaf (-11)) (.branch 41 (.leaf (-8)) (.leaf (-5))))),
  (.branch 24 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-6)))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 40 (.branch 39 (.leaf (-9)) (.leaf (-7))) (.branch 41 (.leaf (-5)) (.leaf (-3)))),
  (.branch 39 (.branch 37 (.leaf (-13)) (.branch 38 (.leaf (-11)) (.leaf (-9)))) (.branch 40 (.leaf (-7)) (.branch 41 (.leaf (-5)) (.leaf (-3))))),
  (.branch 16 (.leaf (-4)) (.leaf (-3))),
  (.branch 40 (.branch 28 (.leaf (-6)) (.leaf (-5))) (.branch 41 (.leaf (-4)) (.leaf (-3)))),
  (.branch 26 (.branch 18 (.branch 14 (.branch 12 (.branch 11 (.leaf (-32)) (.leaf (-31))) (.branch 13 (.leaf (-30)) (.leaf (-29)))) (.branch 16 (.branch 15 (.leaf (-28)) (.leaf (-27))) (.branch 17 (.leaf (-26)) (.leaf (-25))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-24)) (.leaf (-23))) (.branch 21 (.leaf (-22)) (.leaf (-21)))) (.branch 24 (.branch 23 (.leaf (-20)) (.leaf (-19))) (.branch 25 (.leaf (-18)) (.leaf (-17)))))) (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6710 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (3)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (6)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (3)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (7)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (3)) (.leaf (2))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (6)) (.branch 30 (.leaf (2)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (3)) (.leaf (1))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (0)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (5)) (.branch 38 (.leaf (3)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (8)) (.leaf (2))))))))
  code := certificateP9_6710
  counts := ![(.branch 19 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 22 (.leaf (-13)) (.leaf (-14)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 12 (.leaf (-14)) (.leaf (-15)))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 30 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-15)) (.leaf (-16)))),
  (.branch 16 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-13))),
  (.branch 20 (.leaf (0)) (.leaf (-22))),
  (.branch 41 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 36 (.branch 23 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-10)) (.leaf (-6)))),
  (.branch 40 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.branch 37 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-1)) (.leaf (0))))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-14))) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 32 (.branch 30 (.leaf (-13)) (.branch 31 (.leaf (-12)) (.leaf (-11)))) (.branch 33 (.leaf (-10)) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 25 (.branch 22 (.branch 21 (.leaf (-22)) (.leaf (-21))) (.branch 23 (.leaf (-20)) (.branch 24 (.leaf (-19)) (.leaf (-18))))) (.branch 28 (.branch 26 (.leaf (-17)) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_322_6711 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (6)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (7))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (3))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (8)))) (.branch 19 (.leaf (5)) (.branch 20 (.leaf (1)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (6)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (7))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (5)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (2)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (8)))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_6711
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 16 (.leaf (-14)) (.branch 37 (.leaf (-16)) (.leaf (-17))))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 21 (.branch 15 (.leaf (0)) (.leaf (-1))) (.branch 36 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-15)) (.leaf (-16)))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (-1))) (.branch 40 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 7 (.leaf (0)) (.leaf (-14))),
  (.branch 18 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 39 (.branch 38 (.leaf (-17)) (.leaf (-14))) (.branch 40 (.leaf (-11)) (.branch 41 (.leaf (-8)) (.leaf (-5))))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.branch 40 (.leaf (-1)) (.leaf (0))))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-14))) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 41 (.leaf (-4)) (.leaf (-3))),
  (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_322_6712 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (6)) (.leaf (8))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (3))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (7))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (2)) (.leaf (3))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (1)))) (.branch 19 (.leaf (4)) (.branch 20 (.leaf (6)) (.leaf (7))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (5)) (.leaf (8))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (4))) (.branch 29 (.leaf (6)) (.branch 30 (.leaf (0)) (.leaf (2)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (3)) (.leaf (7))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (1)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (6)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (5)) (.leaf (7))))))))
  code := certificateP9_6712
  counts := ![(.branch 16 (.branch 1 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 41 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-32))) (.branch 18 (.leaf (-34)) (.leaf (-36)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-12))) (.branch 39 (.leaf (-14)) (.leaf (-15)))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (-7))) (.branch 40 (.leaf (-9)) (.leaf (-10)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-27))) (.branch 19 (.leaf (-29)) (.leaf (-31)))),
  (.branch 8 (.leaf (0)) (.branch 41 (.leaf (-1)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-9)) (.leaf (-11)))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 39 (.branch 23 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.branch 36 (.branch 19 (.leaf (-36)) (.leaf (-35))) (.branch 37 (.leaf (-30)) (.leaf (-25)))) (.branch 40 (.branch 39 (.leaf (-20)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 41 (.leaf (-10)) (.leaf (-5))),
  (.branch 38 (.branch 20 (.leaf (-31)) (.branch 37 (.leaf (-30)) (.leaf (-25)))) (.branch 40 (.branch 39 (.leaf (-20)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-3)),
  (.branch 39 (.branch 21 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-9)))) (.branch 40 (.leaf (-7)) (.branch 41 (.leaf (-5)) (.leaf (-3))))),
  (.branch 22 (.leaf (-1)) (.leaf (0))),
  (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6713 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (7))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (3)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (8))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (6)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_6713
  counts := ![(.branch 20 (.branch 8 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))) (.branch 32 (.branch 25 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 34 (.leaf (14)) (.leaf (15))) (.branch 39 (.leaf (16)) (.branch 41 (.leaf (17)) (.leaf (18))))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.branch 28 (.leaf (-6)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-18))),
  (.branch 14 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-30))),
  (.branch 33 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 37 (.leaf (-4)) (.leaf (-3))),
  (.branch 39 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 27 (.leaf (-11)) (.branch 38 (.leaf (-10)) (.leaf (-8)))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 41 (.leaf (-4)) (.leaf (-2))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-9)))) (.branch 32 (.leaf (-8)) (.branch 33 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 35 (.leaf (-5)) (.branch 36 (.leaf (-4)) (.leaf (-3)))) (.branch 38 (.leaf (-2)) (.branch 39 (.leaf (-1)) (.leaf (0)))))),
  (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-14)) (.leaf (-13))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 19 (.branch 15 (.branch 13 (.leaf (-30)) (.branch 14 (.leaf (-29)) (.leaf (-28)))) (.branch 17 (.branch 16 (.leaf (-27)) (.leaf (-26))) (.branch 18 (.leaf (-25)) (.leaf (-24))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-23)) (.leaf (-22))) (.branch 22 (.leaf (-21)) (.leaf (-20)))) (.branch 25 (.branch 24 (.leaf (-19)) (.leaf (-18))) (.branch 26 (.leaf (-17)) (.leaf (-16)))))) (.branch 34 (.branch 30 (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6714 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (7)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (5)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (8)) (.leaf (3)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (4)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (7)) (.leaf (0))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (4)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (6))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (5)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (8)) (.leaf (2)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (4)) (.leaf (3))))))))
  code := certificateP9_6714
  counts := ![(.branch 19 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))) (.branch 25 (.leaf (-12)) (.branch 28 (.leaf (-13)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 21 (.leaf (-5)) (.branch 29 (.leaf (-6)) (.leaf (-7))))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 12 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 17 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 33 (.branch 29 (.leaf (-15)) (.leaf (-14))) (.branch 37 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-9))))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 30 (.leaf (-7)) (.leaf (-6))) (.branch 41 (.leaf (-5)) (.leaf (-4)))),
  (.branch 35 (.leaf (-2)) (.branch 36 (.leaf (-1)) (.leaf (0)))),
  (.branch 31 (.leaf (-3)) (.leaf (-2))),
  (.branch 38 (.branch 36 (.branch 25 (.leaf (-15)) (.leaf (-14))) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 30 (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_322_6715 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (7)) (.leaf (6)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (5)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (8)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (6)) (.branch 25 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (7)) (.leaf (5)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (6)) (.leaf (0)))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (8)) (.leaf (2))))))))
  code := certificateP9_6715
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-4)) (.leaf (-6)))) (.branch 27 (.leaf (-8)) (.branch 37 (.leaf (-9)) (.leaf (-11))))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-12))),
  (.branch 20 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))),
  (.leaf (0)),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_322_6716 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (7)) (.leaf (3))) (.branch 8 (.leaf (6)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (8))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 19 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (8)) (.leaf (3))) (.branch 29 (.leaf (6)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (4)) (.leaf (7))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (5)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (3)) (.leaf (0)))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (8)) (.leaf (4))))))))
  code := certificateP9_6716
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 13 (.leaf (-14)) (.branch 34 (.leaf (-16)) (.leaf (-17))))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.branch 33 (.leaf (-8)) (.leaf (-9)))),
  (.branch 12 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 40 (.branch 35 (.leaf (-17)) (.leaf (-14))) (.branch 41 (.leaf (-10)) (.leaf (-6)))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.branch 26 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 38 (.branch 36 (.branch 25 (.leaf (-15)) (.leaf (-14))) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 30 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_322_6717 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (0)) (.leaf (6)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (8)) (.branch 20 (.leaf (2)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (6)) (.branch 25 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (7)) (.branch 30 (.leaf (0)) (.leaf (5)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (4)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (6)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 40 (.leaf (8)) (.branch 41 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_6717
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-13)) (.leaf (-14)))) (.branch 17 (.leaf (-15)) (.branch 38 (.leaf (-17)) (.leaf (-18))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 12 (.leaf (-14)) (.leaf (-15)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 10 (.leaf (0)) (.branch 37 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.leaf (-13))),
  (.branch 19 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-14))) (.branch 41 (.leaf (-10)) (.leaf (-6)))),
  (.branch 40 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-1)),
  (.branch 38 (.branch 26 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 36 (.branch 33 (.branch 17 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 32 (.branch 30 (.leaf (-13)) (.branch 31 (.leaf (-12)) (.leaf (-11)))) (.branch 33 (.leaf (-10)) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_322_6718 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (6)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (7)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (5)) (.branch 20 (.leaf (2)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (6)) (.branch 25 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (3)) (.leaf (8)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_6718
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 17 (.leaf (-11)) (.branch 38 (.leaf (-13)) (.leaf (-14))))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 37 (.leaf (-6)) (.leaf (-8)))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-2)) (.leaf (-3)))),
  (.branch 19 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-18))),
  (.branch 10 (.leaf (0)) (.leaf (-32))),
  (.branch 31 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-11))) (.branch 41 (.leaf (-8)) (.leaf (-5)))),
  (.leaf (-1)),
  (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4))))),
  (.branch 35 (.branch 34 (.leaf (-3)) (.leaf (-2))) (.branch 36 (.leaf (-1)) (.leaf (0)))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-14)) (.leaf (-13))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 18 (.branch 14 (.branch 12 (.branch 11 (.leaf (-32)) (.leaf (-31))) (.branch 13 (.leaf (-30)) (.leaf (-29)))) (.branch 16 (.branch 15 (.leaf (-28)) (.leaf (-27))) (.branch 17 (.leaf (-26)) (.leaf (-25))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-24)) (.leaf (-23))) (.branch 21 (.leaf (-22)) (.leaf (-21)))) (.branch 24 (.branch 23 (.leaf (-20)) (.leaf (-19))) (.branch 25 (.leaf (-18)) (.leaf (-17)))))) (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6719 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (7)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (8)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (5)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (6)) (.branch 20 (.leaf (4)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (7)) (.branch 25 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (1))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (2)) (.leaf (8)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (4)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_6719
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 17 (.leaf (-11)) (.branch 38 (.leaf (-13)) (.leaf (-14))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 37 (.leaf (-6)) (.leaf (-8)))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 27 (.leaf (0)) (.leaf (-1))),
  (.branch 19 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-18))),
  (.branch 10 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-11))) (.branch 41 (.leaf (-8)) (.leaf (-5)))),
  (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4))))),
  (.branch 35 (.branch 34 (.leaf (-3)) (.leaf (-2))) (.branch 36 (.leaf (-1)) (.leaf (0)))),
  (.branch 38 (.branch 36 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-14)) (.leaf (-13))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6720 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (7)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (8)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (7)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (1)) (.leaf (5))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (4))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (8)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (6))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (0)) (.leaf (7)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (3))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (5)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (1)) (.leaf (8)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_6720
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_322_6721 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (7)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (5))) (.branch 8 (.leaf (6)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (3))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (6))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (5)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (2)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (8)) (.branch 25 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (4)) (.leaf (3))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (6))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (5)) (.leaf (0)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_6721
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-7)) (.leaf (-8)))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (-5))) (.branch 36 (.leaf (-11)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-39))),
  (.branch 24 (.leaf (0)) (.leaf (-18)))]
  high := ![(.branch 40 (.branch 27 (.leaf (-17)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 26 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 39 (.branch 37 (.leaf (-16)) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11))))),
  (.branch 22 (.branch 12 (.branch 7 (.branch 5 (.branch 4 (.leaf (-39)) (.leaf (-38))) (.branch 6 (.leaf (-37)) (.leaf (-36)))) (.branch 9 (.branch 8 (.leaf (-35)) (.leaf (-34))) (.branch 10 (.leaf (-33)) (.branch 11 (.leaf (-32)) (.leaf (-31)))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (-30)) (.leaf (-29))) (.branch 15 (.leaf (-28)) (.branch 16 (.leaf (-27)) (.leaf (-26))))) (.branch 19 (.branch 18 (.leaf (-25)) (.leaf (-24))) (.branch 20 (.leaf (-23)) (.branch 21 (.leaf (-22)) (.leaf (-21))))))) (.branch 32 (.branch 27 (.branch 24 (.branch 23 (.leaf (-20)) (.leaf (-19))) (.branch 25 (.leaf (-18)) (.branch 26 (.leaf (-17)) (.leaf (-16))))) (.branch 29 (.branch 28 (.leaf (-15)) (.leaf (-14))) (.branch 30 (.leaf (-13)) (.branch 31 (.leaf (-12)) (.leaf (-11)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6))))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-14)) (.leaf (-13))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_322_6722 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (7)) (.branch 4 (.leaf (6)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (8)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (7))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (6)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (8)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (5)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (7)) (.branch 25 (.leaf (6)) (.leaf (4))))) (.branch 28 (.branch 27 (.leaf (8)) (.leaf (1))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (3)) (.leaf (5)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (7))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (6)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (8)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (5)) (.leaf (4))))))))
  code := certificateP9_6722
  counts := ![(.branch 16 (.branch 1 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-6))),
  (.branch 2 (.leaf (0)) (.leaf (-32))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (-7))) (.branch 23 (.leaf (-9)) (.leaf (-11)))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-17))) (.branch 21 (.leaf (-19)) (.leaf (-21)))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 33 (.leaf (-10)) (.leaf (-11)))),
  (.branch 6 (.leaf (0)) (.branch 27 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 39 (.branch 30 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.branch 20 (.branch 3 (.leaf (-32)) (.leaf (-31))) (.branch 37 (.leaf (-30)) (.leaf (-25)))) (.branch 40 (.branch 39 (.leaf (-20)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.branch 24 (.leaf (-11)) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 39 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.leaf (-2)),
  (.branch 38 (.branch 36 (.leaf (-14)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.leaf (-8)))) (.branch 39 (.branch 38 (.leaf (-7)) (.leaf (-6))) (.branch 40 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 40 (.branch 28 (.leaf (-6)) (.leaf (-5))) (.branch 41 (.leaf (-4)) (.leaf (-3))))]
def witnessP9_322_6723 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (5)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (7)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (5)) (.branch 20 (.leaf (1)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (0)) (.leaf (6))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (5)) (.leaf (2)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (8))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_6723
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 35 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 28 (.leaf (-21)) (.branch 35 (.leaf (-22)) (.leaf (-23))))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-22))) (.branch 37 (.leaf (-24)) (.leaf (-25)))),
  (.branch 8 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-7)))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-16))),
  (.branch 16 (.leaf (0)) (.leaf (-26))),
  (.branch 36 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 40 (.branch 36 (.leaf (-23)) (.leaf (-21))) (.branch 41 (.leaf (-16)) (.leaf (-11)))),
  (.leaf (-1)),
  (.branch 39 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 38 (.leaf (-25)) (.leaf (-20))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.branch 25 (.branch 16 (.leaf (-7)) (.leaf (-6))) (.branch 34 (.leaf (-5)) (.branch 35 (.leaf (-2)) (.leaf (0))))),
  (.branch 41 (.leaf (-4)) (.leaf (-2))),
  (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.branch 22 (.branch 19 (.branch 17 (.leaf (-26)) (.branch 18 (.leaf (-25)) (.leaf (-24)))) (.branch 20 (.leaf (-23)) (.branch 21 (.leaf (-22)) (.leaf (-21))))) (.branch 25 (.branch 23 (.leaf (-20)) (.branch 24 (.leaf (-19)) (.leaf (-18)))) (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))))) (.branch 35 (.branch 32 (.branch 30 (.leaf (-13)) (.branch 31 (.leaf (-12)) (.leaf (-11)))) (.branch 33 (.leaf (-10)) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_322_6724 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (8)) (.leaf (6)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (5))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (4)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (7)) (.leaf (6))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (5))))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (4))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (8)) (.leaf (6)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (3)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (5))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (4)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (7)) (.leaf (6))))))))
  code := certificateP9_6724
  counts := ![(.branch 17 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 22 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-10)) (.leaf (-14)))) (.branch 25 (.leaf (-15)) (.branch 29 (.leaf (-16)) (.leaf (-17))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 37 (.leaf (-8)) (.leaf (-11)))),
  (.branch 27 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 35 (.leaf (-14)) (.leaf (-15)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 20 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 39 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-10)) (.leaf (-7))))),
  (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))),
  (.branch 38 (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-13)) (.leaf (-11)))) (.branch 40 (.branch 39 (.leaf (-9)) (.leaf (-7))) (.branch 41 (.leaf (-5)) (.leaf (-3))))),
  (.branch 15 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-3)))),
  (.branch 40 (.branch 29 (.leaf (-7)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-10)) (.leaf (-8)))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6725 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (3)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (7)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (2))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (8)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (6))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (5))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (7)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (4)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (8)) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (1)) (.leaf (6))))))))
  code := certificateP9_6725
  counts := ![(.branch 20 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 24 (.leaf (5)) (.leaf (6))) (.branch 34 (.leaf (7)) (.branch 38 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 27 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (7)) (.branch 41 (.leaf (8)) (.leaf (9)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 12 (.leaf (-14)) (.leaf (-15)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.branch 32 (.leaf (-9)) (.leaf (-10)))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-12))),
  (.branch 16 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 40 (.branch 39 (.leaf (-12)) (.leaf (-9))) (.branch 41 (.leaf (-6)) (.leaf (-3)))),
  (.branch 32 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 40 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.branch 38 (.branch 36 (.leaf (-14)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 37 (.branch 34 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6))))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_322_6726 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (0)) (.leaf (7))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (6)) (.branch 20 (.leaf (1)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (4)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (0)) (.leaf (3)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (2))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (0)) (.leaf (8))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_6726
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 24 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 9 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 27 (.leaf (-14)) (.leaf (-15)))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 34 (.leaf (-9)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.leaf (-13))),
  (.branch 19 (.leaf (0)) (.leaf (-2))),
  (.branch 15 (.leaf (0)) (.leaf (-27))),
  (.branch 36 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 40 (.branch 31 (.leaf (-18)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 33 (.leaf (-8)) (.leaf (-5))),
  (.branch 39 (.branch 28 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-11)) (.branch 41 (.leaf (-8)) (.leaf (-5))))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-9))) (.branch 37 (.leaf (-8)) (.leaf (-7)))) (.branch 40 (.branch 39 (.leaf (-6)) (.leaf (-5))) (.branch 41 (.leaf (-4)) (.leaf (-3))))),
  (.branch 35 (.branch 32 (.branch 30 (.leaf (-13)) (.branch 31 (.leaf (-12)) (.leaf (-11)))) (.branch 33 (.leaf (-10)) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 28 (.branch 21 (.branch 18 (.branch 16 (.leaf (-27)) (.branch 17 (.leaf (-26)) (.leaf (-25)))) (.branch 19 (.leaf (-24)) (.branch 20 (.leaf (-23)) (.leaf (-22))))) (.branch 24 (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19)))) (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))))) (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_322_6727 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (7)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (0)))) (.branch 19 (.leaf (8)) (.branch 20 (.leaf (1)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (7)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (0)) (.leaf (3)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (4)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (6)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (5)) (.leaf (0)))) (.branch 40 (.leaf (8)) (.branch 41 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_6727
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 25 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 9 (.leaf (-17)) (.branch 13 (.leaf (-18)) (.leaf (-19))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-10)) (.leaf (-11)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4)))),
  (.branch 14 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 19 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 40 (.branch 35 (.leaf (-19)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 29 (.leaf (-7)) (.leaf (-6))),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 36 (.branch 33 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 30 (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_322_6728 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (4)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (7)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (6))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (4)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (5)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (8))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (3))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (6))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (7)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (3)) (.leaf (5))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (6)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (1)) (.leaf (8))))))))
  code := certificateP9_6728
  counts := ![(.branch 20 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 24 (.leaf (5)) (.leaf (6))) (.branch 34 (.leaf (7)) (.branch 38 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 27 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (7)) (.branch 41 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (-3)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-9)) (.leaf (-10)))),
  (.branch 12 (.leaf (0)) (.branch 39 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.branch 40 (.branch 39 (.leaf (-12)) (.leaf (-9))) (.branch 41 (.leaf (-6)) (.leaf (-3)))),
  (.branch 32 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 38 (.branch 20 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 40 (.branch 39 (.leaf (-9)) (.leaf (-7))) (.branch 41 (.leaf (-5)) (.leaf (-3))))),
  (.branch 41 (.leaf (-5)) (.leaf (-3))),
  (.branch 38 (.branch 36 (.leaf (-14)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 37 (.branch 34 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6))))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_322_6729 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (5)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (7))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (5))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (6)) (.leaf (0)))) (.branch 19 (.leaf (4)) (.branch 20 (.leaf (1)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (8))) (.branch 29 (.leaf (1)) (.branch 30 (.leaf (4)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (3)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (5))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (6)) (.leaf (0)))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_6729
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 24 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-16))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 2 (.leaf (0)) (.leaf (-17))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-6)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-35))),
  (.branch 28 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 40 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 25 (.leaf (-6)) (.leaf (-5))),
  (.branch 37 (.branch 35 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 36 (.leaf (-14)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-10)) (.leaf (-8))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (0)),
  (.branch 41 (.leaf (-4)) (.leaf (-2))),
  (.branch 38 (.branch 26 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 39 (.branch 27 (.leaf (-7)) (.leaf (-6))) (.branch 40 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-3))))),
  (.branch 24 (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-35)) (.leaf (-34))) (.branch 10 (.leaf (-33)) (.leaf (-32)))) (.branch 13 (.branch 12 (.leaf (-31)) (.leaf (-30))) (.branch 14 (.leaf (-29)) (.leaf (-28))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-27)) (.leaf (-26))) (.branch 18 (.leaf (-25)) (.leaf (-24)))) (.branch 21 (.branch 20 (.leaf (-23)) (.leaf (-22))) (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19))))))) (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-14)) (.leaf (-13))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6730 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (6)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (7)) (.branch 14 (.leaf (0)) (.leaf (6))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (4)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (5))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (6)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (0)) (.leaf (5)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (3))) (.branch 34 (.leaf (8)) (.branch 35 (.leaf (0)) (.leaf (6))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (1)) (.leaf (4)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (3)) (.leaf (5))))))))
  code := certificateP9_6730
  counts := ![(.branch 19 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 22 (.leaf (-9)) (.branch 30 (.leaf (-10)) (.leaf (-12))))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 13 (.leaf (0)) (.leaf (-29))),
  (.branch 34 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 36 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 41 (.leaf (-10)) (.leaf (-8)))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 30 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.branch 29 (.leaf (-7)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 38 (.branch 26 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 27 (.branch 20 (.branch 16 (.branch 14 (.leaf (-29)) (.branch 15 (.leaf (-28)) (.leaf (-27)))) (.branch 18 (.branch 17 (.leaf (-26)) (.leaf (-25))) (.branch 19 (.leaf (-24)) (.leaf (-23))))) (.branch 23 (.branch 21 (.leaf (-22)) (.branch 22 (.leaf (-21)) (.leaf (-20)))) (.branch 25 (.branch 24 (.leaf (-19)) (.leaf (-18))) (.branch 26 (.leaf (-17)) (.leaf (-16)))))) (.branch 34 (.branch 30 (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_322_6731 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (7))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (5))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (6)) (.branch 20 (.leaf (3)) (.leaf (1))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (8))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (4)) (.leaf (1))))))))
  code := certificateP9_6731
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 25 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 38 (.leaf (8)) (.branch 42 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 41 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-16)) (.leaf (-17)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 27 (.leaf (-12)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-9))),
  (.branch 19 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-35))),
  (.branch 28 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 40 (.branch 27 (.leaf (-17)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 39 (.branch 30 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.branch 28 (.leaf (-14)) (.branch 37 (.leaf (-13)) (.leaf (-11)))) (.branch 40 (.branch 39 (.leaf (-9)) (.leaf (-7))) (.branch 41 (.leaf (-5)) (.leaf (-3))))),
  (.branch 7 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 24 (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-35)) (.leaf (-34))) (.branch 10 (.leaf (-33)) (.leaf (-32)))) (.branch 13 (.branch 12 (.leaf (-31)) (.leaf (-30))) (.branch 14 (.leaf (-29)) (.leaf (-28))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-27)) (.leaf (-26))) (.branch 18 (.leaf (-25)) (.leaf (-24)))) (.branch 21 (.branch 20 (.leaf (-23)) (.leaf (-22))) (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19))))))) (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-14)) (.leaf (-13))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6732 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (6))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (7)) (.leaf (1))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (2))) (.branch 29 (.leaf (1)) (.branch 30 (.leaf (0)) (.leaf (3)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (6))))) (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (8)) (.leaf (1))))))))
  code := certificateP9_6732
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 25 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 38 (.leaf (8)) (.branch 42 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 9 (.leaf (-17)) (.branch 13 (.leaf (-18)) (.leaf (-19))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 14 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 35 (.leaf (-10)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 10 (.leaf (0)) (.branch 37 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-6))),
  (.branch 20 (.leaf (0)) (.leaf (-22))),
  (.branch 41 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 40 (.branch 35 (.leaf (-19)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.leaf (-3)) (.leaf (0))),
  (.branch 36 (.leaf (-12)) (.branch 41 (.leaf (-10)) (.leaf (-7)))),
  (.branch 36 (.branch 33 (.branch 17 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 30 (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 25 (.branch 22 (.branch 21 (.leaf (-22)) (.leaf (-21))) (.branch 23 (.leaf (-20)) (.branch 24 (.leaf (-19)) (.leaf (-18))))) (.branch 28 (.branch 26 (.leaf (-17)) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_322_6733 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (0))) (.branch 8 (.leaf (6)) (.branch 9 (.leaf (7)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (8)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (5)) (.leaf (6)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (7)) (.leaf (8))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (1))) (.branch 29 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (8)) (.leaf (2))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (6)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (7)) (.leaf (8))))))))
  code := certificateP9_6733
  counts := ![(.branch 19 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 12 (.leaf (-17)) (.leaf (-18)))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.leaf (0))]
  high := ![(.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-18)) (.leaf (-16))) (.branch 36 (.leaf (-14)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-10)) (.leaf (-8))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 38 (.branch 36 (.branch 25 (.leaf (-15)) (.leaf (-14))) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-10)) (.leaf (-8)))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 39 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 31 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0))]
def witnessP9_322_6734 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (7))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (6))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (2)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (1))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (1)) (.leaf (5))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (8))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (3)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (6))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (4)) (.leaf (2)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (3)) (.leaf (1))))))))
  code := certificateP9_6734
  counts := ![(.branch 19 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 25 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 42 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 22 (.leaf (-13)) (.leaf (-14)))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-3)))) (.branch 33 (.leaf (-4)) (.branch 37 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-8)))),
  (.branch 17 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-16))),
  (.branch 15 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-35))),
  (.branch 28 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 36 (.branch 23 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-10)) (.leaf (-6)))),
  (.branch 38 (.leaf (-6)) (.branch 39 (.leaf (-3)) (.leaf (0)))),
  (.branch 40 (.branch 24 (.leaf (-13)) (.leaf (-12))) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.branch 33 (.leaf (-8)) (.leaf (-7))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-35)) (.leaf (-34))) (.branch 10 (.leaf (-33)) (.leaf (-32)))) (.branch 13 (.branch 12 (.leaf (-31)) (.leaf (-30))) (.branch 14 (.leaf (-29)) (.leaf (-28))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-27)) (.leaf (-26))) (.branch 18 (.leaf (-25)) (.leaf (-24)))) (.branch 21 (.branch 20 (.leaf (-23)) (.leaf (-22))) (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19))))))) (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-14)) (.leaf (-13))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6735 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (7))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (1)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (3)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (6)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (1)) (.leaf (5))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (8))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (1)) (.leaf (4)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (6)) (.branch 35 (.leaf (1)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (5)) (.branch 38 (.leaf (0)) (.leaf (3)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (6)) (.leaf (4))))))))
  code := certificateP9_6735
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 11 (.leaf (-18)) (.leaf (-19)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 14 (.leaf (-6)) (.branch 19 (.leaf (-7)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 24 (.leaf (-6)) (.branch 39 (.leaf (-8)) (.leaf (-9))))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (-6)) (.leaf (-11)))),
  (.branch 7 (.leaf (0)) (.leaf (-35))),
  (.branch 28 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 39 (.branch 33 (.leaf (-19)) (.leaf (-16))) (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-8)) (.leaf (-4))))),
  (.branch 41 (.leaf (-8)) (.leaf (-4))),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7)))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 39 (.branch 27 (.leaf (-11)) (.branch 38 (.leaf (-10)) (.leaf (-8)))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-11)),
  (.branch 24 (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-35)) (.leaf (-34))) (.branch 10 (.leaf (-33)) (.leaf (-32)))) (.branch 13 (.branch 12 (.leaf (-31)) (.leaf (-30))) (.branch 14 (.leaf (-29)) (.leaf (-28))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-27)) (.leaf (-26))) (.branch 18 (.leaf (-25)) (.leaf (-24)))) (.branch 21 (.branch 20 (.leaf (-23)) (.leaf (-22))) (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19))))))) (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-14)) (.leaf (-13))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6736 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (7))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (8)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (1)))) (.branch 19 (.leaf (6)) (.branch 20 (.leaf (0)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (0)) (.leaf (7))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (3))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (5)) (.leaf (2)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (4))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (8)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_6736
  counts := ![(.branch 20 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 25 (.leaf (5)) (.leaf (6))) (.branch 34 (.leaf (7)) (.branch 39 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 27 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (7)) (.branch 41 (.leaf (8)) (.leaf (9)))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-2)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 28 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-12))),
  (.branch 19 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 35 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-6)) (.leaf (-3))))),
  (.branch 37 (.leaf (-4)) (.leaf (-3))),
  (.branch 39 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 29 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-9)))) (.branch 40 (.leaf (-7)) (.branch 41 (.leaf (-5)) (.leaf (-3))))),
  (.branch 25 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (0)))),
  (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_322_6737 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (4)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (3)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (6)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 19 (.leaf (4)) (.branch 20 (.leaf (1)) (.leaf (7))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (3)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (6)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (1)) (.leaf (8))))))))
  code := certificateP9_6737
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 11 (.leaf (-18)) (.leaf (-19)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.branch 20 (.leaf (-3)) (.leaf (-4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 12 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 25 (.leaf (-5)) (.branch 40 (.leaf (-7)) (.leaf (-8))))),
  (.branch 8 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-7))),
  (.branch 21 (.leaf (0)) (.leaf (-21))),
  (.leaf (0))]
  high := ![(.branch 39 (.branch 33 (.leaf (-19)) (.leaf (-16))) (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-4)),
  (.branch 40 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 41 (.leaf (-8)) (.leaf (-7))),
  (.branch 35 (.branch 32 (.branch 30 (.leaf (-13)) (.branch 31 (.leaf (-12)) (.leaf (-11)))) (.branch 33 (.leaf (-10)) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 24 (.leaf (-19)) (.branch 25 (.leaf (-18)) (.leaf (-17))))) (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_322_6738 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (5)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (3)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (4)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 19 (.leaf (5)) (.branch 20 (.leaf (1)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (6)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (8)) (.branch 30 (.leaf (3)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (4)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_6738
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 11 (.leaf (-18)) (.leaf (-19)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.branch 20 (.leaf (-3)) (.leaf (-4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 12 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 21 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-21))),
  (.branch 13 (.leaf (0)) (.branch 25 (.leaf (-3)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.leaf (-34))),
  (.branch 29 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 39 (.branch 33 (.leaf (-19)) (.leaf (-16))) (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-4)),
  (.branch 40 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 37 (.branch 22 (.leaf (-5)) (.branch 36 (.leaf (-4)) (.leaf (-3)))) (.branch 38 (.leaf (-2)) (.branch 39 (.leaf (-1)) (.leaf (0))))),
  (.branch 37 (.branch 20 (.branch 5 (.leaf (-21)) (.leaf (-20))) (.branch 35 (.leaf (-19)) (.branch 36 (.leaf (-17)) (.leaf (-15))))) (.branch 39 (.branch 38 (.leaf (-13)) (.leaf (-11))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-7)) (.leaf (-5)))))),
  (.branch 26 (.leaf (-8)) (.branch 41 (.leaf (-7)) (.leaf (-5)))),
  (.branch 25 (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-34)) (.leaf (-33))) (.branch 11 (.leaf (-32)) (.leaf (-31)))) (.branch 14 (.branch 13 (.leaf (-30)) (.leaf (-29))) (.branch 15 (.leaf (-28)) (.leaf (-27))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-26)) (.leaf (-25))) (.branch 19 (.leaf (-24)) (.leaf (-23)))) (.branch 22 (.branch 21 (.leaf (-22)) (.leaf (-21))) (.branch 23 (.leaf (-20)) (.branch 24 (.leaf (-19)) (.leaf (-18))))))) (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 35 (.branch 32 (.branch 30 (.leaf (-13)) (.branch 31 (.leaf (-12)) (.leaf (-11)))) (.branch 33 (.leaf (-10)) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6739 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (8)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (5)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (7)) (.branch 14 (.leaf (2)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 19 (.leaf (6)) (.branch 20 (.leaf (2)) (.leaf (1))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (8)) (.leaf (2))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (7)) (.branch 35 (.leaf (3)) (.leaf (5))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (3)) (.leaf (1))))))))
  code := certificateP9_6739
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 10 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 22 (.leaf (-13)) (.leaf (-14)))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-23)) (.leaf (-28)))),
  (.branch 9 (.leaf (0)) (.branch 36 (.leaf (-11)) (.leaf (-15)))),
  (.branch 19 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 34 (.branch 23 (.leaf (-14)) (.leaf (-13))) (.branch 40 (.leaf (-11)) (.branch 41 (.leaf (-8)) (.leaf (-5))))),
  (.branch 32 (.leaf (-3)) (.branch 38 (.leaf (-1)) (.leaf (0)))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 35 (.branch 32 (.branch 16 (.leaf (-28)) (.branch 31 (.leaf (-27)) (.leaf (-25)))) (.branch 33 (.leaf (-23)) (.branch 34 (.leaf (-21)) (.leaf (-19))))) (.branch 38 (.branch 36 (.leaf (-17)) (.branch 37 (.leaf (-15)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-11)) (.leaf (-9))) (.branch 41 (.leaf (-7)) (.leaf (-5)))))),
  (.branch 39 (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-13)) (.leaf (-11)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-7)) (.leaf (-5))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_322_6740 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (6)) (.branch 4 (.leaf (1)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (6))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (0)) (.leaf (7))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 19 (.leaf (5)) (.branch 20 (.leaf (0)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (6)) (.branch 25 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (1))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (2)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (3)) (.leaf (6))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (1)) (.leaf (8))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (3)))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_6740
  counts := ![(.branch 20 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 33 (.leaf (-10)) (.leaf (-11)))),
  (.branch 15 (.leaf (0)) (.leaf (-27))),
  (.branch 36 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 39 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.leaf (-1)) (.leaf (0))),
  (.branch 30 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.leaf (-8)))) (.branch 39 (.branch 38 (.leaf (-7)) (.leaf (-6))) (.branch 40 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 28 (.branch 21 (.branch 18 (.branch 16 (.leaf (-27)) (.branch 17 (.leaf (-26)) (.leaf (-25)))) (.branch 19 (.leaf (-24)) (.branch 20 (.leaf (-23)) (.leaf (-22))))) (.branch 24 (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19)))) (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))))) (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_322_6741 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (7)) (.branch 4 (.leaf (1)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (8))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (0)) (.leaf (6))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 19 (.leaf (5)) (.branch 20 (.leaf (0)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (7)) (.branch 25 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (1))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (2)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (3)) (.leaf (8))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (1)) (.leaf (6))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (3)))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_6741
  counts := ![(.branch 20 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 15 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-18))),
  (.branch 12 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 39 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.leaf (-1)) (.leaf (0))),
  (.branch 30 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-14)) (.leaf (-13))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6742 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (4)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (3)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (7)) (.leaf (3))))) (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (6)) (.branch 20 (.leaf (2)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (3)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (5))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (8)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6742
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 22 (.leaf (-7)) (.branch 32 (.leaf (-8)) (.leaf (-10))))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-22))) (.branch 37 (.leaf (-24)) (.leaf (-25)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-8)) (.leaf (-13)))),
  (.branch 14 (.leaf (0)) (.leaf (-28))),
  (.branch 35 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 40 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.leaf (-7)))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 38 (.leaf (-25)) (.leaf (-20))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.branch 17 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (0)))),
  (.branch 27 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))),
  (.branch 28 (.branch 21 (.branch 17 (.branch 15 (.leaf (-28)) (.branch 16 (.leaf (-27)) (.leaf (-26)))) (.branch 19 (.branch 18 (.leaf (-25)) (.leaf (-24))) (.branch 20 (.leaf (-23)) (.leaf (-22))))) (.branch 24 (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19)))) (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))))) (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_322_6743 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (6)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (7))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (8)) (.leaf (1))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (6)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (7)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (1)) (.leaf (8))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (4)) (.leaf (2))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (7))) (.branch 29 (.leaf (1)) (.branch 30 (.leaf (4)) (.leaf (2)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (8)) (.leaf (5))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (6)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (4)) (.leaf (7)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (5)) (.leaf (8))))))))
  code := certificateP9_6743
  counts := ![(.branch 17 (.branch 1 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 41 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.leaf (-37))) (.branch 17 (.leaf (-39)) (.leaf (-41)))),
  (.branch 3 (.leaf (0)) (.leaf (-27))),
  (.branch 6 (.leaf (0)) (.branch 31 (.leaf (-12)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-32)) (.leaf (-34)))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-17))) (.branch 38 (.leaf (-19)) (.leaf (-20)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (-2))) (.branch 24 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 37 (.branch 35 (.branch 18 (.leaf (-41)) (.leaf (-40))) (.branch 36 (.leaf (-35)) (.leaf (-30)))) (.branch 39 (.branch 38 (.leaf (-25)) (.leaf (-20))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 38 (.branch 4 (.leaf (-27)) (.branch 21 (.leaf (-26)) (.leaf (-25)))) (.branch 40 (.branch 39 (.leaf (-20)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.branch 32 (.leaf (-13)) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 38 (.branch 28 (.branch 11 (.leaf (-34)) (.leaf (-33))) (.branch 37 (.leaf (-30)) (.leaf (-25)))) (.branch 40 (.branch 39 (.leaf (-20)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.branch 40 (.branch 39 (.leaf (-20)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 25 (.leaf (-6)) (.leaf (-5))),
  (.branch 38 (.branch 36 (.leaf (-14)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 40 (.branch 29 (.leaf (-7)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0))]
def witnessP9_322_6744 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (7))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (3)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (6)) (.leaf (3))))) (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (8)) (.branch 20 (.leaf (1)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (5)) (.leaf (7))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (3)) (.leaf (2)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (5))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (6)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (8)) (.branch 41 (.leaf (1)) (.leaf (5))))))))
  code := certificateP9_6744
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 22 (.leaf (-7)) (.branch 32 (.leaf (-8)) (.leaf (-10))))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-22))) (.branch 37 (.leaf (-24)) (.leaf (-25)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-4)))),
  (.branch 14 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-16))),
  (.branch 19 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 40 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.leaf (-7)))),
  (.leaf (-1)),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 38 (.leaf (-25)) (.leaf (-20))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.branch 17 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (0)))),
  (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_322_6745 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (6)) (.branch 4 (.leaf (1)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (4)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (3)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (7)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (6)) (.branch 25 (.leaf (1)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (1)) (.leaf (4)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (6))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (3)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (4)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (8)) (.leaf (2))))))))
  code := certificateP9_6745
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 11 (.leaf (-18)) (.branch 16 (.leaf (-19)) (.leaf (-20))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 13 (.leaf (-4)) (.branch 34 (.leaf (-7)) (.leaf (-9))))),
  (.leaf (0)),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 18 (.leaf (-14)) (.branch 26 (.leaf (-15)) (.leaf (-16))))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-7)) (.leaf (-8)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 33 (.leaf (-10)) (.leaf (-11)))),
  (.branch 20 (.leaf (0)) (.leaf (-22))),
  (.branch 41 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 39 (.branch 38 (.leaf (-20)) (.leaf (-16))) (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-8)) (.leaf (-4))))),
  (.branch 35 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 38 (.branch 36 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-13)) (.leaf (-11)))) (.branch 40 (.branch 39 (.leaf (-9)) (.leaf (-7))) (.branch 41 (.leaf (-5)) (.leaf (-3))))),
  (.branch 40 (.leaf (-7)) (.branch 41 (.leaf (-5)) (.leaf (-3)))),
  (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.leaf (-8)))) (.branch 39 (.branch 38 (.leaf (-7)) (.leaf (-6))) (.branch 40 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 31 (.branch 25 (.branch 22 (.branch 21 (.leaf (-22)) (.leaf (-21))) (.branch 23 (.leaf (-20)) (.branch 24 (.leaf (-19)) (.leaf (-18))))) (.branch 28 (.branch 26 (.leaf (-17)) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_322_6746 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (8)) (.branch 4 (.leaf (1)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (7))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (4)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (3)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (6)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (8)) (.branch 25 (.leaf (1)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (1)) (.leaf (4)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (7))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (3)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (4)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (6)) (.leaf (2))))))))
  code := certificateP9_6746
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 11 (.leaf (-18)) (.branch 16 (.leaf (-19)) (.leaf (-20))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 13 (.leaf (-4)) (.branch 34 (.leaf (-7)) (.leaf (-9))))),
  (.leaf (0)),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 18 (.leaf (-14)) (.branch 26 (.leaf (-15)) (.leaf (-16))))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-7)) (.leaf (-8)))),
  (.branch 20 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.leaf (-18)))]
  high := ![(.branch 39 (.branch 38 (.leaf (-20)) (.leaf (-16))) (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-8)) (.leaf (-4))))),
  (.branch 35 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 38 (.branch 36 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-13)) (.leaf (-11)))) (.branch 40 (.branch 39 (.leaf (-9)) (.leaf (-7))) (.branch 41 (.leaf (-5)) (.leaf (-3))))),
  (.branch 40 (.leaf (-7)) (.branch 41 (.leaf (-5)) (.leaf (-3)))),
  (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1)),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-14)) (.leaf (-13))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_322_6747 : CycleWitness 9 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (8)) (.branch 4 (.leaf (1)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (5))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (7)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (6)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (8)) (.leaf (1)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (2)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (7))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (1)) (.leaf (2))))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (6))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (4)) (.leaf (8)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (5))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (7)) (.branch 38 (.leaf (4)) (.leaf (1)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (5)) (.leaf (6))))))))
  code := certificateP9_6747
  counts := ![(.branch 15 (.branch 1 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 41 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-32))) (.branch 35 (.leaf (-34)) (.leaf (-35)))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-17))) (.branch 21 (.leaf (-19)) (.leaf (-21)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 38 (.branch 36 (.leaf (-35)) (.branch 37 (.leaf (-30)) (.leaf (-25)))) (.branch 40 (.branch 39 (.leaf (-20)) (.leaf (-15))) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.branch 39 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.branch 8 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6748 : CycleWitness 9 where
  length := 41
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (0))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (5))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (7))) (.branch 23 (.leaf (1)) (.branch 24 (.leaf (0)) (.leaf (4))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (1)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (5)) (.leaf (2))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (8))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (4)))) (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_6748
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 24 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 27 (.leaf (9)) (.leaf (10)))) (.branch 36 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 39 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-27)) (.leaf (-35)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 23 (.leaf (-6)) (.branch 34 (.leaf (-7)) (.leaf (-8))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 37 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.branch 38 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-9)) (.leaf (-11)))),
  (.branch 6 (.leaf (0)) (.leaf (-35))),
  (.branch 22 (.leaf (0)) (.leaf (-19))),
  (.branch 35 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 28 (.branch 22 (.branch 19 (.leaf (-35)) (.leaf (-34))) (.branch 25 (.leaf (-33)) (.leaf (-32)))) (.branch 34 (.branch 31 (.leaf (-31)) (.leaf (-30))) (.branch 37 (.leaf (-29)) (.branch 40 (.leaf (-28)) (.leaf (-14)))))),
  (.leaf (-8)),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 39 (.leaf (-9)) (.branch 40 (.leaf (-6)) (.leaf (-3)))),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 38 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 39 (.leaf (-4)) (.branch 40 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 23 (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-35)) (.leaf (-34))) (.branch 9 (.leaf (-33)) (.leaf (-32)))) (.branch 12 (.branch 11 (.leaf (-31)) (.leaf (-30))) (.branch 13 (.leaf (-29)) (.leaf (-28))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-27)) (.leaf (-26))) (.branch 17 (.leaf (-25)) (.leaf (-24)))) (.branch 20 (.branch 19 (.leaf (-23)) (.leaf (-22))) (.branch 21 (.leaf (-21)) (.branch 22 (.leaf (-20)) (.leaf (-19))))))) (.branch 32 (.branch 27 (.branch 25 (.branch 24 (.leaf (-18)) (.leaf (-17))) (.branch 26 (.leaf (-16)) (.leaf (-15)))) (.branch 29 (.branch 28 (.leaf (-14)) (.leaf (-13))) (.branch 30 (.leaf (-12)) (.branch 31 (.leaf (-11)) (.leaf (-10)))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-9)) (.leaf (-8))) (.branch 35 (.leaf (-7)) (.leaf (-6)))) (.branch 38 (.branch 37 (.leaf (-5)) (.leaf (-4))) (.branch 39 (.leaf (-3)) (.branch 40 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 31 (.branch 26 (.branch 24 (.branch 23 (.leaf (-19)) (.leaf (-18))) (.branch 25 (.leaf (-17)) (.leaf (-16)))) (.branch 28 (.branch 27 (.leaf (-15)) (.leaf (-14))) (.branch 29 (.leaf (-13)) (.branch 30 (.leaf (-12)) (.leaf (-11)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-10)) (.leaf (-9))) (.branch 34 (.leaf (-8)) (.branch 35 (.leaf (-7)) (.leaf (-6))))) (.branch 38 (.branch 37 (.leaf (-5)) (.leaf (-4))) (.branch 39 (.leaf (-3)) (.branch 40 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-5)) (.leaf (-4)))) (.branch 39 (.leaf (-3)) (.branch 40 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_322_6749 : CycleWitness 9 where
  length := 41
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (5))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (6))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (5)) (.branch 19 (.leaf (0)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (4)) (.leaf (2))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (3)) (.leaf (7))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (4)) (.branch 29 (.leaf (5)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (0)) (.leaf (4))))) (.branch 38 (.branch 36 (.leaf (2)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 39 (.leaf (8)) (.branch 40 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_6749
  counts := ![(.branch 19 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 34 (.leaf (9)) (.branch 38 (.leaf (10)) (.leaf (11)))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 41 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 16 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 19 (.leaf (-15)) (.branch 34 (.leaf (-19)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 37 (.leaf (-27)) (.leaf (-28)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-4)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-7)) (.branch 35 (.leaf (-8)) (.leaf (-10))))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-29))),
  (.branch 25 (.leaf (0)) (.leaf (-16))),
  (.branch 39 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 39 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 40 (.leaf (-14)) (.leaf (-9)))),
  (.branch 39 (.branch 38 (.leaf (-28)) (.leaf (-21))) (.branch 40 (.leaf (-14)) (.leaf (-7)))),
  (.branch 38 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 39 (.leaf (-4)) (.branch 40 (.leaf (-3)) (.leaf (-2))))),
  (.branch 25 (.branch 7 (.leaf (-8)) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 34 (.leaf (-5)) (.branch 35 (.leaf (-2)) (.leaf (0))))),
  (.branch 38 (.branch 36 (.leaf (-10)) (.branch 37 (.leaf (-9)) (.leaf (-8)))) (.branch 39 (.leaf (-7)) (.branch 40 (.leaf (-6)) (.leaf (-5))))),
  (.branch 19 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.leaf (-8)))),
  (.branch 26 (.branch 19 (.branch 15 (.branch 13 (.leaf (-29)) (.branch 14 (.leaf (-28)) (.leaf (-27)))) (.branch 17 (.branch 16 (.leaf (-26)) (.leaf (-25))) (.branch 18 (.leaf (-24)) (.leaf (-23))))) (.branch 22 (.branch 20 (.leaf (-22)) (.branch 21 (.leaf (-21)) (.leaf (-20)))) (.branch 24 (.branch 23 (.leaf (-19)) (.leaf (-18))) (.branch 25 (.leaf (-17)) (.leaf (-16)))))) (.branch 33 (.branch 29 (.branch 27 (.leaf (-15)) (.branch 28 (.leaf (-14)) (.leaf (-13)))) (.branch 31 (.branch 30 (.leaf (-12)) (.leaf (-11))) (.branch 32 (.leaf (-10)) (.leaf (-9))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-8)) (.leaf (-7))) (.branch 36 (.leaf (-6)) (.leaf (-5)))) (.branch 39 (.branch 38 (.leaf (-4)) (.leaf (-3))) (.branch 40 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-16)) (.leaf (-15))) (.branch 28 (.leaf (-14)) (.leaf (-13)))) (.branch 31 (.branch 30 (.leaf (-12)) (.leaf (-11))) (.branch 32 (.leaf (-10)) (.leaf (-9))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-8)) (.leaf (-7))) (.branch 36 (.leaf (-6)) (.leaf (-5)))) (.branch 39 (.branch 38 (.leaf (-4)) (.leaf (-3))) (.branch 40 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_322_6750 : CycleWitness 9 where
  length := 41
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (6))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (7)) (.branch 19 (.leaf (0)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (4)) (.leaf (2))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (3)) (.leaf (5))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (4)) (.branch 29 (.leaf (6)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (0)) (.leaf (4))))) (.branch 38 (.branch 36 (.leaf (2)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 39 (.leaf (5)) (.branch 40 (.leaf (8)) (.leaf (3))))))))
  code := certificateP9_6750
  counts := ![(.branch 19 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 34 (.leaf (9)) (.branch 38 (.leaf (10)) (.leaf (11)))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 41 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 16 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 19 (.leaf (-15)) (.branch 34 (.leaf (-19)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 37 (.leaf (-27)) (.leaf (-28)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-4)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-7)) (.branch 35 (.leaf (-8)) (.leaf (-10))))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-14))),
  (.branch 18 (.leaf (0)) (.leaf (-23))),
  (.branch 40 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 39 (.branch 35 (.leaf (-20)) (.leaf (-19))) (.branch 40 (.leaf (-14)) (.leaf (-9)))),
  (.branch 39 (.branch 38 (.leaf (-28)) (.leaf (-21))) (.branch 40 (.leaf (-14)) (.leaf (-7)))),
  (.branch 38 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 39 (.leaf (-4)) (.branch 40 (.leaf (-3)) (.leaf (-2))))),
  (.branch 25 (.branch 7 (.leaf (-8)) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 34 (.leaf (-5)) (.branch 35 (.leaf (-2)) (.leaf (0))))),
  (.branch 38 (.branch 36 (.leaf (-10)) (.branch 37 (.leaf (-9)) (.leaf (-8)))) (.branch 39 (.leaf (-7)) (.branch 40 (.leaf (-6)) (.leaf (-5))))),
  (.branch 26 (.leaf (-7)) (.branch 40 (.leaf (-6)) (.leaf (-3)))),
  (.branch 34 (.branch 31 (.branch 8 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 32 (.leaf (-11)) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 37 (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 29 (.branch 23 (.branch 20 (.branch 19 (.leaf (-23)) (.leaf (-22))) (.branch 21 (.leaf (-21)) (.branch 22 (.leaf (-20)) (.leaf (-19))))) (.branch 26 (.branch 24 (.leaf (-18)) (.branch 25 (.leaf (-17)) (.leaf (-16)))) (.branch 27 (.leaf (-15)) (.branch 28 (.leaf (-14)) (.leaf (-13)))))) (.branch 35 (.branch 32 (.branch 30 (.leaf (-12)) (.branch 31 (.leaf (-11)) (.leaf (-10)))) (.branch 33 (.leaf (-9)) (.branch 34 (.leaf (-8)) (.leaf (-7))))) (.branch 38 (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-5)) (.leaf (-4)))) (.branch 39 (.leaf (-3)) (.branch 40 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_322_6751 : CycleWitness 9 where
  length := 41
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (4)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (6)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (3))) (.branch 18 (.leaf (5)) (.branch 19 (.leaf (7)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (4))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (4))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (6)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (3)) (.leaf (1))) (.branch 33 (.leaf (5)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (4)) (.branch 37 (.leaf (1)) (.leaf (3)))) (.branch 39 (.leaf (0)) (.branch 40 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_6751
  counts := ![(.branch 21 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 25 (.leaf (5)) (.leaf (6))) (.branch 35 (.leaf (7)) (.branch 39 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 29 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 37 (.leaf (-27)) (.leaf (-28)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-19)) (.leaf (-32)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-8)) (.leaf (-10)))),
  (.branch 9 (.leaf (0)) (.leaf (-23))),
  (.branch 19 (.leaf (0)) (.leaf (-22))),
  (.leaf (0))]
  high := ![(.branch 40 (.leaf (-6)) (.leaf (-5))),
  (.branch 39 (.branch 38 (.leaf (-28)) (.leaf (-21))) (.branch 40 (.leaf (-14)) (.leaf (-7)))),
  (.leaf (-2)),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (-23)) (.leaf (-22))) (.branch 18 (.leaf (-21)) (.leaf (-20)))) (.branch 39 (.branch 32 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-12)) (.leaf (-6))))),
  (.branch 38 (.branch 28 (.leaf (-32)) (.branch 37 (.leaf (-31)) (.leaf (-27)))) (.branch 39 (.leaf (-23)) (.branch 40 (.leaf (-19)) (.leaf (-15))))),
  (.branch 36 (.branch 34 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.leaf (-7)))) (.branch 38 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 39 (.leaf (-4)) (.branch 40 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 35 (.branch 32 (.branch 10 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-20)))) (.branch 33 (.leaf (-18)) (.branch 34 (.leaf (-16)) (.leaf (-14))))) (.branch 38 (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-10)) (.leaf (-8)))) (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 30 (.branch 24 (.branch 21 (.branch 20 (.leaf (-22)) (.leaf (-21))) (.branch 22 (.leaf (-20)) (.branch 23 (.leaf (-19)) (.leaf (-18))))) (.branch 27 (.branch 25 (.leaf (-17)) (.branch 26 (.leaf (-16)) (.leaf (-15)))) (.branch 28 (.leaf (-14)) (.branch 29 (.leaf (-13)) (.leaf (-12)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-11)) (.leaf (-10))) (.branch 33 (.leaf (-9)) (.branch 34 (.leaf (-8)) (.leaf (-7))))) (.branch 38 (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-5)) (.leaf (-4)))) (.branch 39 (.leaf (-3)) (.branch 40 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_322_6752 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 6 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (7))))) (.branch 16 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 17 (.leaf (4)) (.branch 19 (.leaf (0)) (.leaf (5)))))) (.branch 30 (.branch 26 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (0)))) (.branch 27 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (8))))) (.branch 36 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (0)))) (.branch 37 (.leaf (4)) (.branch 39 (.leaf (0)) (.leaf (6)))))))
  code := certificateP9_6752
  counts := ![(.branch 19 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (5)) (.leaf (6))))) (.branch 13 (.branch 11 (.leaf (7)) (.branch 12 (.leaf (8)) (.leaf (9)))) (.branch 16 (.branch 15 (.leaf (10)) (.leaf (11))) (.branch 18 (.leaf (12)) (.leaf (13)))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (14)) (.branch 22 (.leaf (15)) (.leaf (16)))) (.branch 26 (.branch 25 (.leaf (17)) (.leaf (18))) (.branch 28 (.leaf (19)) (.leaf (20))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (21)) (.leaf (22))) (.branch 33 (.leaf (23)) (.leaf (24)))) (.branch 38 (.branch 36 (.leaf (25)) (.leaf (26))) (.branch 39 (.leaf (27)) (.leaf (28))))))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 3 (.leaf (-6)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-30))),
  (.branch 30 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 34 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7)))),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0)),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.leaf (-30)) (.branch 12 (.leaf (-29)) (.leaf (-28)))) (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.leaf (-20)))) (.branch 23 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.leaf (-16)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6753 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (6)))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (7)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (6)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.leaf (8)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (5))))))))
  code := certificateP9_6753
  counts := ![(.branch 19 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))))) (.branch 29 (.branch 22 (.branch 21 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.branch 26 (.leaf (13)) (.leaf (14))))) (.branch 34 (.branch 31 (.leaf (15)) (.branch 32 (.leaf (16)) (.leaf (17)))) (.branch 36 (.leaf (18)) (.branch 39 (.leaf (19)) (.leaf (20))))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-25))),
  (.branch 35 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 37 (.leaf (-2)) (.leaf (-1))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 21 (.branch 18 (.branch 16 (.leaf (-25)) (.branch 17 (.leaf (-24)) (.leaf (-23)))) (.branch 19 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20))))) (.branch 24 (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17)))) (.branch 25 (.leaf (-16)) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_322_6754 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (2))) (.branch 9 (.leaf (0)) (.leaf (5))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (7))) (.branch 19 (.leaf (0)) (.leaf (6)))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (5))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (8))) (.branch 39 (.leaf (0)) (.leaf (6)))))))
  code := certificateP9_6754
  counts := ![(.branch 19 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 14 (.branch 11 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))) (.branch 16 (.leaf (9)) (.branch 17 (.leaf (10)) (.leaf (11)))))) (.branch 29 (.branch 24 (.branch 21 (.leaf (12)) (.branch 22 (.leaf (13)) (.leaf (14)))) (.branch 26 (.leaf (15)) (.branch 27 (.leaf (16)) (.leaf (17))))) (.branch 34 (.branch 31 (.leaf (18)) (.branch 32 (.leaf (19)) (.leaf (20)))) (.branch 37 (.branch 36 (.leaf (21)) (.leaf (22))) (.branch 39 (.leaf (23)) (.leaf (24))))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 18 (.leaf (0)) (.leaf (-22))),
  (.branch 38 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 38 (.leaf (-4)) (.leaf (-3))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 29 (.branch 23 (.branch 20 (.branch 19 (.leaf (-22)) (.leaf (-21))) (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18))))) (.branch 26 (.branch 24 (.leaf (-17)) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_322_6755 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (1)))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (4)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (8)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (3)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (6)) (.leaf (1)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (0)) (.leaf (4)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (7)) (.leaf (2))))))))
  code := certificateP9_6755
  counts := ![(.branch 18 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))))) (.branch 28 (.branch 22 (.branch 21 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.branch 26 (.leaf (13)) (.leaf (14))))) (.branch 34 (.branch 31 (.leaf (15)) (.branch 32 (.leaf (16)) (.leaf (17)))) (.branch 36 (.leaf (18)) (.branch 38 (.leaf (19)) (.leaf (20))))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-31))),
  (.branch 29 (.leaf (0)) (.leaf (-11))),
  (.branch 39 (.leaf (0)) (.leaf (-1))),
  (.branch 19 (.leaf (0)) (.leaf (-21)))]
  high := ![(.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 31 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.leaf (-31)) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17))))) (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_322_6756 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (5)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (8)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (6)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (1)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.leaf (7)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (1))))))))
  code := certificateP9_6756
  counts := ![(.branch 18 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))))) (.branch 28 (.branch 22 (.branch 21 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.branch 26 (.leaf (13)) (.leaf (14))))) (.branch 34 (.branch 31 (.leaf (15)) (.branch 32 (.leaf (16)) (.leaf (17)))) (.branch 36 (.leaf (18)) (.branch 38 (.leaf (19)) (.leaf (20))))))),
  (.branch 20 (.branch 10 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 9 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 39 (.leaf (0)) (.leaf (-1))),
  (.branch 19 (.leaf (0)) (.leaf (-21))),
  (.branch 5 (.leaf (0)) (.leaf (-35))),
  (.branch 25 (.leaf (0)) (.leaf (-15))),
  (.branch 35 (.leaf (0)) (.leaf (-5))),
  (.branch 15 (.leaf (0)) (.leaf (-25)))]
  high := ![(.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.leaf (-1)) (.leaf (0))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17))))) (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-35)) (.leaf (-34))) (.branch 8 (.leaf (-33)) (.leaf (-32)))) (.branch 11 (.branch 10 (.leaf (-31)) (.leaf (-30))) (.branch 12 (.leaf (-29)) (.leaf (-28))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))))) (.branch 31 (.branch 26 (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 28 (.branch 27 (.leaf (-14)) (.leaf (-13))) (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 21 (.branch 18 (.branch 16 (.leaf (-25)) (.branch 17 (.leaf (-24)) (.leaf (-23)))) (.branch 19 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20))))) (.branch 24 (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17)))) (.branch 25 (.leaf (-16)) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_322_6757 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (4)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (6)) (.branch 9 (.leaf (0)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (4)) (.leaf (0))) (.branch 18 (.leaf (7)) (.branch 19 (.leaf (1)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (5)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (1))) (.branch 28 (.leaf (6)) (.branch 29 (.leaf (0)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (5)) (.leaf (0))) (.branch 38 (.leaf (8)) (.branch 39 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_6757
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 22 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 25 (.leaf (9)) (.leaf (10)))) (.branch 34 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 37 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 22 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-22))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-19)) (.leaf (-22)))),
  (.branch 10 (.leaf (0)) (.branch 36 (.leaf (-7)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-22))),
  (.branch 38 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-1)),
  (.branch 36 (.branch 34 (.branch 7 (.leaf (-22)) (.leaf (-21))) (.branch 35 (.leaf (-18)) (.leaf (-15)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-9))) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 27 (.leaf (-2)) (.leaf (0))),
  (.branch 34 (.branch 31 (.branch 17 (.leaf (-22)) (.leaf (-21))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-17)) (.leaf (-15))))) (.branch 37 (.branch 35 (.leaf (-13)) (.branch 36 (.leaf (-11)) (.leaf (-9)))) (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-7))) (.branch 39 (.leaf (-5)) (.leaf (-3)))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.branch 23 (.branch 20 (.branch 19 (.leaf (-22)) (.leaf (-21))) (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18))))) (.branch 26 (.branch 24 (.leaf (-17)) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_322_6758 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (6))) (.branch 9 (.leaf (0)) (.leaf (1))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (7))) (.branch 19 (.leaf (0)) (.leaf (1)))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (8))) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (0)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (5))) (.branch 39 (.leaf (0)) (.leaf (1)))))))
  code := certificateP9_6758
  counts := ![(.branch 19 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 14 (.branch 11 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))) (.branch 16 (.leaf (9)) (.branch 17 (.leaf (10)) (.leaf (11)))))) (.branch 29 (.branch 24 (.branch 21 (.leaf (12)) (.branch 22 (.leaf (13)) (.leaf (14)))) (.branch 26 (.leaf (15)) (.branch 27 (.leaf (16)) (.leaf (17))))) (.branch 34 (.branch 31 (.leaf (18)) (.branch 32 (.leaf (19)) (.leaf (20)))) (.branch 37 (.branch 36 (.leaf (21)) (.leaf (22))) (.branch 39 (.leaf (23)) (.leaf (24))))))),
  (.branch 20 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-27))),
  (.branch 33 (.leaf (0)) (.leaf (-7))),
  (.branch 38 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-32))),
  (.branch 18 (.leaf (0)) (.leaf (-22))),
  (.branch 28 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 38 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 19 (.branch 16 (.branch 14 (.leaf (-27)) (.branch 15 (.leaf (-26)) (.leaf (-25)))) (.branch 17 (.leaf (-24)) (.branch 18 (.leaf (-23)) (.leaf (-22))))) (.branch 22 (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19)))) (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))))) (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-32)) (.leaf (-31))) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 23 (.branch 20 (.branch 19 (.leaf (-22)) (.leaf (-21))) (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18))))) (.branch 26 (.branch 24 (.leaf (-17)) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6759 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (4)))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (6)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (7)) (.leaf (4)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (0)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (8)) (.leaf (4))))))))
  code := certificateP9_6759
  counts := ![(.branch 18 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))))) (.branch 28 (.branch 22 (.branch 21 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.branch 26 (.leaf (13)) (.leaf (14))))) (.branch 34 (.branch 31 (.leaf (15)) (.branch 32 (.leaf (16)) (.leaf (17)))) (.branch 36 (.leaf (18)) (.branch 38 (.leaf (19)) (.leaf (20))))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-31))),
  (.branch 19 (.leaf (0)) (.leaf (-21))),
  (.branch 29 (.leaf (0)) (.leaf (-11))),
  (.branch 39 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.leaf (-31)) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17))))) (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_322_6760 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (7))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (0)))) (.branch 17 (.branch 16 (.leaf (6)) (.leaf (0))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (8))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (5)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (3)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (6)) (.leaf (0))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_6760
  counts := ![(.branch 19 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 10 (.leaf (5)) (.branch 12 (.leaf (6)) (.leaf (7)))) (.branch 15 (.leaf (8)) (.branch 17 (.leaf (9)) (.leaf (10)))))) (.branch 30 (.branch 24 (.branch 21 (.leaf (11)) (.branch 22 (.leaf (12)) (.leaf (13)))) (.branch 26 (.leaf (14)) (.branch 28 (.leaf (15)) (.leaf (16))))) (.branch 35 (.branch 32 (.leaf (17)) (.branch 34 (.leaf (18)) (.leaf (19)))) (.branch 37 (.leaf (20)) (.branch 39 (.leaf (21)) (.leaf (22))))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 22 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-33))),
  (.branch 27 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 36 (.branch 23 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.leaf (-8)))),
  (.branch 32 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-33)) (.leaf (-32))) (.branch 10 (.leaf (-31)) (.leaf (-30)))) (.branch 13 (.branch 12 (.leaf (-29)) (.leaf (-28))) (.branch 14 (.leaf (-27)) (.leaf (-26))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-25)) (.leaf (-24))) (.branch 18 (.leaf (-23)) (.leaf (-22)))) (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.leaf (-18)))))) (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6761 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (7)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (2)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (6)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (0))) (.branch 28 (.leaf (5)) (.branch 29 (.leaf (0)) (.leaf (8)))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (0)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (6)) (.leaf (4))))))))
  code := certificateP9_6761
  counts := ![(.branch 18 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 15 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))))) (.branch 29 (.branch 22 (.branch 21 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14))))) (.branch 35 (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17)))) (.branch 37 (.leaf (18)) (.branch 38 (.leaf (19)) (.leaf (20))))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (-15)) (.leaf (-17)))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-30))),
  (.branch 30 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 37 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 24 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-17)) (.leaf (-15))) (.branch 35 (.leaf (-13)) (.leaf (-11)))) (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-7))) (.branch 39 (.leaf (-5)) (.leaf (-3))))),
  (.branch 13 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (0)))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.leaf (-30)) (.branch 12 (.leaf (-29)) (.leaf (-28)))) (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.leaf (-20)))) (.branch 23 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.leaf (-16)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6762 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (5)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (4))) (.branch 9 (.leaf (0)) (.leaf (1))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (6)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1)))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (7)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (0)) (.leaf (8)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (0)) (.leaf (1)))))))
  code := certificateP9_6762
  counts := ![(.branch 19 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 14 (.branch 11 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))) (.branch 16 (.leaf (9)) (.branch 17 (.leaf (10)) (.leaf (11)))))) (.branch 29 (.branch 24 (.branch 21 (.leaf (12)) (.branch 22 (.leaf (13)) (.leaf (14)))) (.branch 26 (.leaf (15)) (.branch 27 (.leaf (16)) (.leaf (17))))) (.branch 34 (.branch 31 (.leaf (18)) (.branch 32 (.leaf (19)) (.leaf (20)))) (.branch 37 (.branch 36 (.leaf (21)) (.leaf (22))) (.branch 39 (.leaf (23)) (.leaf (24))))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 5 (.leaf (0)) (.leaf (-35))),
  (.branch 15 (.leaf (0)) (.leaf (-25))),
  (.branch 25 (.leaf (0)) (.leaf (-15))),
  (.branch 35 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 38 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-35)) (.leaf (-34))) (.branch 8 (.leaf (-33)) (.leaf (-32)))) (.branch 11 (.branch 10 (.leaf (-31)) (.leaf (-30))) (.branch 12 (.leaf (-29)) (.leaf (-28))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))))) (.branch 31 (.branch 26 (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 28 (.branch 27 (.leaf (-14)) (.leaf (-13))) (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 27 (.branch 21 (.branch 18 (.branch 16 (.leaf (-25)) (.branch 17 (.leaf (-24)) (.leaf (-23)))) (.branch 19 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20))))) (.branch 24 (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17)))) (.branch 25 (.leaf (-16)) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_322_6763 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (5)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (6))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (5)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (8)) (.branch 29 (.leaf (0)) (.leaf (3)))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (6))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (1))))))))
  code := certificateP9_6763
  counts := ![(.branch 18 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 15 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))))) (.branch 29 (.branch 22 (.branch 21 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14))))) (.branch 35 (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17)))) (.branch 37 (.leaf (18)) (.branch 38 (.leaf (19)) (.leaf (20))))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 32 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-32))),
  (.branch 28 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 33 (.leaf (-3)) (.leaf (-2))) (.branch 35 (.leaf (-1)) (.leaf (0)))),
  (.branch 36 (.branch 24 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-32)) (.leaf (-31))) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6764 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (7))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (5))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (1)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (8))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (2))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (6))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (1))))))))
  code := certificateP9_6764
  counts := ![(.branch 18 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 22 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 25 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 30 (.leaf (12)) (.leaf (13))) (.branch 35 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 24 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 22 (.leaf (-22)) (.leaf (-26)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 31 (.leaf (-7)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-8)) (.leaf (-9)))),
  (.branch 26 (.leaf (0)) (.branch 39 (.leaf (-2)) (.leaf (-3)))),
  (.branch 17 (.leaf (0)) (.leaf (-23))),
  (.branch 37 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-33))),
  (.branch 27 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 36 (.branch 23 (.leaf (-26)) (.leaf (-25))) (.branch 39 (.leaf (-22)) (.leaf (-15)))),
  (.branch 37 (.branch 32 (.leaf (-12)) (.leaf (-9))) (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-1)) (.leaf (0))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 20 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7)))) (.branch 38 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 39 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 28 (.branch 22 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-33)) (.leaf (-32))) (.branch 10 (.leaf (-31)) (.leaf (-30)))) (.branch 13 (.branch 12 (.leaf (-29)) (.leaf (-28))) (.branch 14 (.leaf (-27)) (.leaf (-26))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-25)) (.leaf (-24))) (.branch 18 (.leaf (-23)) (.leaf (-22)))) (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.leaf (-18)))))) (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6765 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (0)))) (.branch 17 (.branch 16 (.leaf (7)) (.leaf (0))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (6))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (4)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (8)) (.leaf (0))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (2))))))))
  code := certificateP9_6765
  counts := ![(.branch 19 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 10 (.leaf (5)) (.branch 12 (.leaf (6)) (.leaf (7)))) (.branch 15 (.leaf (8)) (.branch 17 (.leaf (9)) (.leaf (10)))))) (.branch 30 (.branch 24 (.branch 21 (.leaf (11)) (.branch 22 (.leaf (12)) (.leaf (13)))) (.branch 26 (.leaf (14)) (.branch 28 (.leaf (15)) (.leaf (16))))) (.branch 35 (.branch 32 (.leaf (17)) (.branch 34 (.leaf (18)) (.leaf (19)))) (.branch 37 (.leaf (20)) (.branch 39 (.leaf (21)) (.leaf (22))))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 22 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-7)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-33))),
  (.branch 27 (.leaf (0)) (.leaf (-13))),
  (.branch 16 (.leaf (0)) (.leaf (-24))),
  (.branch 36 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 36 (.branch 23 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.leaf (-8)))),
  (.branch 32 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-33)) (.leaf (-32))) (.branch 10 (.leaf (-31)) (.leaf (-30)))) (.branch 13 (.branch 12 (.leaf (-29)) (.leaf (-28))) (.branch 14 (.leaf (-27)) (.leaf (-26))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-25)) (.leaf (-24))) (.branch 18 (.leaf (-23)) (.leaf (-22)))) (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.leaf (-18)))))) (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 22 (.branch 19 (.branch 17 (.leaf (-24)) (.branch 18 (.leaf (-23)) (.leaf (-22)))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_322_6766 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (0)) (.leaf (5)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (3)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (8)) (.branch 29 (.leaf (0)) (.leaf (6)))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (1))))))))
  code := certificateP9_6766
  counts := ![(.branch 18 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 15 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))))) (.branch 29 (.branch 22 (.branch 21 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14))))) (.branch 35 (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17)))) (.branch 37 (.leaf (18)) (.branch 38 (.leaf (19)) (.leaf (20))))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 32 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-30))),
  (.branch 30 (.leaf (0)) (.leaf (-10))),
  (.branch 8 (.leaf (0)) (.leaf (-32))),
  (.branch 28 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 33 (.leaf (-3)) (.leaf (-2))) (.branch 35 (.leaf (-1)) (.leaf (0)))),
  (.branch 37 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 24 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.leaf (-30)) (.branch 12 (.leaf (-29)) (.leaf (-28)))) (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.leaf (-20)))) (.branch 23 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.leaf (-16)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-32)) (.leaf (-31))) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_322_6767 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (7))) (.branch 4 (.leaf (0)) (.leaf (4)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (6))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (1))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (8))) (.branch 24 (.leaf (0)) (.leaf (4)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (5))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (6))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (1))))))))
  code := certificateP9_6767
  counts := ![(.branch 18 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))) (.branch 29 (.branch 22 (.branch 21 (.leaf (9)) (.leaf (10))) (.branch 24 (.leaf (11)) (.branch 27 (.leaf (12)) (.leaf (13))))) (.branch 34 (.branch 31 (.leaf (14)) (.leaf (15))) (.branch 36 (.leaf (16)) (.branch 38 (.leaf (17)) (.leaf (18))))))),
  (.branch 20 (.branch 10 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-9)) (.leaf (-18)))) (.branch 22 (.leaf (-20)) (.branch 24 (.leaf (-22)) (.leaf (-24))))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-37))),
  (.branch 23 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 32 (.branch 25 (.leaf (-24)) (.leaf (-23))) (.branch 39 (.leaf (-22)) (.leaf (-15)))),
  (.leaf (0)),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 12 (.branch 7 (.branch 5 (.branch 4 (.leaf (-37)) (.leaf (-36))) (.branch 6 (.leaf (-35)) (.leaf (-34)))) (.branch 9 (.branch 8 (.leaf (-33)) (.leaf (-32))) (.branch 10 (.leaf (-31)) (.branch 11 (.leaf (-30)) (.leaf (-29)))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25)))) (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_322_6768 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (6))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (7))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (2)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (5))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (3)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (6))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (8))))))))
  code := certificateP9_6768
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 31 (.branch 25 (.branch 22 (.leaf (7)) (.leaf (8))) (.branch 28 (.leaf (9)) (.leaf (10)))) (.branch 36 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 39 (.leaf (13)) (.leaf (14)))))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-6)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.leaf (0))]
  high := ![(.branch 30 (.branch 24 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 34 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7)))),
  (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_322_6769 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (7)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (2)) (.leaf (4))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (8)) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (3))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (6))))))))
  code := certificateP9_6769
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 16 (.leaf (-4)) (.branch 36 (.leaf (-5)) (.leaf (-6))))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-27))),
  (.branch 33 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 30 (.branch 24 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 38 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 39 (.leaf (-4)) (.leaf (-3)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0)),
  (.branch 26 (.branch 19 (.branch 16 (.branch 14 (.leaf (-27)) (.branch 15 (.leaf (-26)) (.leaf (-25)))) (.branch 17 (.leaf (-24)) (.branch 18 (.leaf (-23)) (.leaf (-22))))) (.branch 22 (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19)))) (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))))) (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_322_6770 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (7)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (6))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (2)) (.leaf (4))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (5)) (.branch 29 (.leaf (0)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (8)) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (6))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_6770
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 16 (.leaf (-4)) (.branch 36 (.leaf (-5)) (.leaf (-6))))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 13 (.leaf (0)) (.leaf (-27))),
  (.branch 33 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 30 (.branch 24 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 38 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 39 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 26 (.branch 19 (.branch 16 (.branch 14 (.leaf (-27)) (.branch 15 (.leaf (-26)) (.leaf (-25)))) (.branch 17 (.leaf (-24)) (.branch 18 (.leaf (-23)) (.leaf (-22))))) (.branch 22 (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19)))) (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))))) (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_322_6771 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (8))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (3)) (.leaf (5))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (7)) (.branch 29 (.leaf (0)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (6)) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (8))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_6771
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-19)) (.leaf (-22)))),
  (.branch 10 (.leaf (0)) (.branch 36 (.leaf (-7)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 17 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 30 (.branch 24 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 31 (.branch 17 (.leaf (-22)) (.leaf (-21))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-17)) (.leaf (-15))))) (.branch 37 (.branch 35 (.leaf (-13)) (.branch 36 (.leaf (-11)) (.leaf (-9)))) (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-7))) (.branch 39 (.leaf (-5)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_322_6772 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (6)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (4)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (7)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (2)) (.leaf (5))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (6)) (.leaf (0))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (3)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (8)) (.leaf (4))))))))
  code := certificateP9_6772
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 16 (.leaf (-4)) (.branch 36 (.leaf (-5)) (.leaf (-6))))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (-19)) (.leaf (-20)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 11 (.leaf (0)) (.leaf (-9))),
  (.branch 19 (.leaf (0)) (.leaf (-21))),
  (.branch 39 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 30 (.branch 24 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 39 (.leaf (-4)) (.leaf (-3)))),
  (.branch 36 (.branch 21 (.leaf (-20)) (.branch 35 (.leaf (-18)) (.leaf (-15)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-9))) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17))))) (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_322_6773 : CycleWitness 9 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (7))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (3))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (6)) (.leaf (0))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (8))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6773
  counts := ![(.branch 18 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 24 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 27 (.leaf (10)) (.leaf (11)))) (.branch 35 (.branch 32 (.leaf (12)) (.leaf (13))) (.branch 38 (.leaf (14)) (.leaf (15)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 16 (.leaf (-10)) (.branch 18 (.leaf (-13)) (.leaf (-16))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-15)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.branch 33 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (-11)) (.leaf (-13)))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-25))),
  (.branch 37 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 33 (.branch 30 (.leaf (-16)) (.leaf (-15))) (.branch 36 (.leaf (-14)) (.branch 39 (.leaf (-13)) (.leaf (-9))))),
  (.branch 37 (.branch 8 (.leaf (-18)) (.leaf (-17))) (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-9)) (.leaf (-5))))),
  (.leaf (-3)),
  (.branch 37 (.branch 35 (.leaf (-13)) (.branch 36 (.leaf (-11)) (.leaf (-9)))) (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-5)) (.leaf (-3))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 32 (.branch 28 (.branch 6 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 21 (.branch 18 (.branch 16 (.leaf (-25)) (.branch 17 (.leaf (-24)) (.leaf (-23)))) (.branch 19 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20))))) (.branch 24 (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17)))) (.branch 25 (.leaf (-16)) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_322 : Fin 72 → CycleWitness 9 := ![witnessP9_322_6702, witnessP9_322_6703, witnessP9_322_6704, witnessP9_322_6705, witnessP9_322_6706, witnessP9_322_6707, witnessP9_322_6708, witnessP9_322_6709, witnessP9_322_6710, witnessP9_322_6711, witnessP9_322_6712, witnessP9_322_6713, witnessP9_322_6714, witnessP9_322_6715, witnessP9_322_6716, witnessP9_322_6717, witnessP9_322_6718, witnessP9_322_6719, witnessP9_322_6720, witnessP9_322_6721, witnessP9_322_6722, witnessP9_322_6723, witnessP9_322_6724, witnessP9_322_6725, witnessP9_322_6726, witnessP9_322_6727, witnessP9_322_6728, witnessP9_322_6729, witnessP9_322_6730, witnessP9_322_6731, witnessP9_322_6732, witnessP9_322_6733, witnessP9_322_6734, witnessP9_322_6735, witnessP9_322_6736, witnessP9_322_6737, witnessP9_322_6738, witnessP9_322_6739, witnessP9_322_6740, witnessP9_322_6741, witnessP9_322_6742, witnessP9_322_6743, witnessP9_322_6744, witnessP9_322_6745, witnessP9_322_6746, witnessP9_322_6747, witnessP9_322_6748, witnessP9_322_6749, witnessP9_322_6750, witnessP9_322_6751, witnessP9_322_6752, witnessP9_322_6753, witnessP9_322_6754, witnessP9_322_6755, witnessP9_322_6756, witnessP9_322_6757, witnessP9_322_6758, witnessP9_322_6759, witnessP9_322_6760, witnessP9_322_6761, witnessP9_322_6762, witnessP9_322_6763, witnessP9_322_6764, witnessP9_322_6765, witnessP9_322_6766, witnessP9_322_6767, witnessP9_322_6768, witnessP9_322_6769, witnessP9_322_6770, witnessP9_322_6771, witnessP9_322_6772, witnessP9_322_6773]
end RealPinwheel.FiveSixths


