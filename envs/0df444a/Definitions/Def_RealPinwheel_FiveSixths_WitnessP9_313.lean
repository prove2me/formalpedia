-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_313
-- name    : RealPinwheel_FiveSixths_WitnessP9_313
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:32:44.026328+00:00
-- url     : https://prove2.me/theorems/bc0ce808-5a03-4521-9447-40689f8ed6f9
-- title:
--   Exact witness block P9_313
-- statement:
--   These exact witnesses represent words 6117 through 6175 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 6117–6175; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_313_6116 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (1)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (7)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (4)) (.leaf (0))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (3)) (.branch 27 (.leaf (2)) (.leaf (1)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (5)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (8)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (4)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (3)) (.leaf (2))))) (.branch 47 (.branch 45 (.leaf (1)) (.branch 46 (.leaf (0)) (.leaf (5)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (0))) (.branch 50 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_6116
  counts := ![(.branch 25 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.leaf (15)))))),
  (.branch 23 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-12))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))) (.branch 31 (.leaf (-10)) (.branch 48 (.leaf (-11)) (.leaf (-12))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 37 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-47))),
  (.branch 21 (.leaf (0)) (.leaf (-30))),
  (.branch 38 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 43 (.branch 36 (.leaf (-12)) (.leaf (-11))) (.branch 50 (.leaf (-10)) (.leaf (-5)))),
  (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-9)) (.leaf (-6)))),
  (.branch 38 (.leaf (-5)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.branch 15 (.branch 9 (.branch 6 (.branch 5 (.leaf (-47)) (.leaf (-46))) (.branch 7 (.leaf (-45)) (.branch 8 (.leaf (-44)) (.leaf (-43))))) (.branch 12 (.branch 10 (.leaf (-42)) (.branch 11 (.leaf (-41)) (.leaf (-40)))) (.branch 13 (.leaf (-39)) (.branch 14 (.leaf (-38)) (.leaf (-37)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (-36)) (.branch 17 (.leaf (-35)) (.leaf (-34)))) (.branch 19 (.leaf (-33)) (.branch 20 (.leaf (-32)) (.leaf (-31))))) (.branch 24 (.branch 22 (.leaf (-30)) (.branch 23 (.leaf (-29)) (.leaf (-28)))) (.branch 25 (.leaf (-27)) (.branch 26 (.leaf (-26)) (.leaf (-25))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (-24)) (.branch 29 (.leaf (-23)) (.leaf (-22)))) (.branch 31 (.leaf (-21)) (.branch 32 (.leaf (-20)) (.leaf (-19))))) (.branch 36 (.branch 34 (.leaf (-18)) (.branch 35 (.leaf (-17)) (.leaf (-16)))) (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 28 (.branch 24 (.branch 22 (.leaf (-30)) (.branch 23 (.leaf (-29)) (.leaf (-28)))) (.branch 26 (.branch 25 (.leaf (-27)) (.leaf (-26))) (.branch 27 (.leaf (-25)) (.leaf (-24))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-23)) (.leaf (-22))) (.branch 31 (.leaf (-21)) (.leaf (-20)))) (.branch 34 (.branch 33 (.leaf (-19)) (.leaf (-18))) (.branch 35 (.leaf (-17)) (.leaf (-16)))))) (.branch 43 (.branch 39 (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))) (.branch 41 (.branch 40 (.leaf (-12)) (.leaf (-11))) (.branch 42 (.leaf (-10)) (.leaf (-9))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-8)) (.leaf (-7))) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))) (.branch 42 (.leaf (-10)) (.branch 43 (.leaf (-9)) (.leaf (-8))))) (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_313_6117 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (4)) (.leaf (8)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1)))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (7)) (.branch 20 (.leaf (4)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (2)) (.leaf (8))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 29 (.leaf (6)) (.branch 30 (.leaf (0)) (.leaf (4))))) (.branch 34 (.branch 32 (.leaf (7)) (.branch 33 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (5))) (.branch 37 (.leaf (3)) (.leaf (8)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (4)))) (.branch 42 (.leaf (6)) (.branch 43 (.leaf (0)) (.leaf (7))))) (.branch 47 (.branch 45 (.leaf (2)) (.branch 46 (.leaf (1)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (3)) (.leaf (5))) (.branch 50 (.leaf (8)) (.leaf (4))))))))
  code := certificateP9_6117
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 45 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 48 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 11 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 13 (.leaf (-15)) (.leaf (-16))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 27 (.leaf (-24)) (.branch 33 (.leaf (-25)) (.leaf (-27))))),
  (.branch 3 (.leaf (0)) (.leaf (-29))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (-13))) (.branch 37 (.leaf (-14)) (.leaf (-16)))),
  (.branch 20 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-35)) (.leaf (-38)))),
  (.branch 6 (.leaf (0)) (.branch 44 (.leaf (-27)) (.leaf (-28)))),
  (.branch 12 (.leaf (0)) (.branch 50 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 49 (.branch 48 (.leaf (-16)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4)))),
  (.branch 48 (.branch 34 (.leaf (-27)) (.branch 47 (.leaf (-26)) (.leaf (-21)))) (.branch 49 (.leaf (-16)) (.branch 50 (.leaf (-11)) (.leaf (-6))))),
  (.branch 47 (.branch 35 (.branch 4 (.leaf (-29)) (.leaf (-28))) (.branch 46 (.leaf (-25)) (.leaf (-21)))) (.branch 49 (.branch 48 (.leaf (-17)) (.leaf (-13))) (.branch 50 (.leaf (-9)) (.leaf (-5))))),
  (.branch 49 (.branch 38 (.leaf (-16)) (.leaf (-13))) (.branch 50 (.leaf (-9)) (.leaf (-5)))),
  (.branch 21 (.leaf (-2)) (.leaf (0))),
  (.branch 24 (.branch 11 (.leaf (-11)) (.leaf (-10))) (.branch 37 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-4))))),
  (.branch 45 (.branch 30 (.branch 17 (.leaf (-38)) (.leaf (-37))) (.branch 43 (.leaf (-36)) (.branch 44 (.leaf (-32)) (.leaf (-28))))) (.branch 48 (.branch 46 (.leaf (-24)) (.branch 47 (.leaf (-20)) (.leaf (-16)))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 47 (.branch 45 (.leaf (-28)) (.branch 46 (.leaf (-24)) (.leaf (-20)))) (.branch 49 (.branch 48 (.leaf (-16)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-4))]
def witnessP9_313_6118 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (5)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (4)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (5)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (0))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (5)) (.branch 27 (.leaf (7)) (.leaf (0)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (1)) (.leaf (4))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (5)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (0)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (4)) (.branch 40 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (5)) (.leaf (8))))) (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (3)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (4)) (.leaf (0))) (.branch 50 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6118
  counts := ![(.branch 25 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.leaf (15)))))),
  (.branch 23 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 40 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-12)) (.leaf (-14)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 23 (.leaf (-6)) (.branch 40 (.leaf (-7)) (.leaf (-8))))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-41))),
  (.branch 27 (.leaf (0)) (.leaf (-24))),
  (.branch 44 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 46 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 50 (.leaf (-10)) (.leaf (-5)))),
  (.branch 48 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4))))),
  (.branch 42 (.leaf (-3)) (.leaf (-2))),
  (.branch 48 (.branch 38 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 40 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 30 (.branch 20 (.branch 15 (.branch 12 (.branch 11 (.leaf (-41)) (.leaf (-40))) (.branch 13 (.leaf (-39)) (.branch 14 (.leaf (-38)) (.leaf (-37))))) (.branch 17 (.branch 16 (.leaf (-36)) (.leaf (-35))) (.branch 18 (.leaf (-34)) (.branch 19 (.leaf (-33)) (.leaf (-32)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-31)) (.leaf (-30))) (.branch 23 (.leaf (-29)) (.branch 24 (.leaf (-28)) (.leaf (-27))))) (.branch 27 (.branch 26 (.leaf (-26)) (.leaf (-25))) (.branch 28 (.leaf (-24)) (.branch 29 (.leaf (-23)) (.leaf (-22))))))) (.branch 40 (.branch 35 (.branch 32 (.branch 31 (.leaf (-21)) (.leaf (-20))) (.branch 33 (.leaf (-19)) (.branch 34 (.leaf (-18)) (.leaf (-17))))) (.branch 37 (.branch 36 (.leaf (-16)) (.leaf (-15))) (.branch 38 (.leaf (-14)) (.branch 39 (.leaf (-13)) (.leaf (-12)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (-24)) (.branch 29 (.leaf (-23)) (.leaf (-22)))) (.branch 31 (.leaf (-21)) (.branch 32 (.leaf (-20)) (.leaf (-19))))) (.branch 36 (.branch 34 (.leaf (-18)) (.branch 35 (.leaf (-17)) (.leaf (-16)))) (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_313_6119 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (3)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (5)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (7)) (.leaf (0))) (.branch 24 (.leaf (2)) (.leaf (1))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (4)) (.leaf (3)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (5))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (4)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (0)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (8)) (.branch 40 (.leaf (0)) (.leaf (2)))) (.branch 42 (.leaf (1)) (.branch 43 (.leaf (0)) (.leaf (4))))) (.branch 47 (.branch 45 (.leaf (3)) (.branch 46 (.leaf (0)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (5)) (.leaf (0))) (.branch 50 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_6119
  counts := ![(.branch 23 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 38 (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 43 (.branch 40 (.leaf (14)) (.leaf (15))) (.branch 46 (.leaf (16)) (.branch 49 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2)))),
  (.branch 14 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-46))),
  (.branch 22 (.leaf (0)) (.leaf (-29))),
  (.branch 39 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 44 (.branch 41 (.leaf (-15)) (.leaf (-14))) (.branch 47 (.leaf (-13)) (.branch 50 (.leaf (-12)) (.leaf (-6))))),
  (.branch 49 (.branch 48 (.leaf (-12)) (.leaf (-9))) (.branch 50 (.leaf (-6)) (.leaf (-3)))),
  (.branch 42 (.leaf (-3)) (.leaf (-2))),
  (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 35 (.leaf (-2)) (.branch 45 (.leaf (-1)) (.leaf (0)))),
  (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 16 (.branch 10 (.branch 7 (.branch 6 (.leaf (-46)) (.leaf (-45))) (.branch 8 (.leaf (-44)) (.branch 9 (.leaf (-43)) (.leaf (-42))))) (.branch 13 (.branch 11 (.leaf (-41)) (.branch 12 (.leaf (-40)) (.leaf (-39)))) (.branch 14 (.leaf (-38)) (.branch 15 (.leaf (-37)) (.leaf (-36)))))) (.branch 22 (.branch 19 (.branch 17 (.leaf (-35)) (.branch 18 (.leaf (-34)) (.leaf (-33)))) (.branch 20 (.leaf (-32)) (.branch 21 (.leaf (-31)) (.leaf (-30))))) (.branch 25 (.branch 23 (.leaf (-29)) (.branch 24 (.leaf (-28)) (.leaf (-27)))) (.branch 26 (.leaf (-26)) (.branch 27 (.leaf (-25)) (.leaf (-24))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 29 (.leaf (-23)) (.leaf (-22))) (.branch 31 (.leaf (-21)) (.branch 32 (.leaf (-20)) (.leaf (-19))))) (.branch 36 (.branch 34 (.leaf (-18)) (.branch 35 (.leaf (-17)) (.leaf (-16)))) (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 29 (.branch 25 (.branch 23 (.leaf (-29)) (.branch 24 (.leaf (-28)) (.leaf (-27)))) (.branch 27 (.branch 26 (.leaf (-26)) (.leaf (-25))) (.branch 28 (.leaf (-24)) (.leaf (-23))))) (.branch 32 (.branch 30 (.leaf (-22)) (.branch 31 (.leaf (-21)) (.leaf (-20)))) (.branch 34 (.branch 33 (.leaf (-19)) (.leaf (-18))) (.branch 35 (.leaf (-17)) (.leaf (-16)))))) (.branch 43 (.branch 39 (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))) (.branch 41 (.branch 40 (.leaf (-12)) (.leaf (-11))) (.branch 42 (.leaf (-10)) (.leaf (-9))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-8)) (.leaf (-7))) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_313_6120 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (8)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (6)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (7)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (1)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (4)) (.leaf (1))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (8)))) (.branch 29 (.leaf (1)) (.branch 30 (.leaf (3)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (6)) (.branch 33 (.leaf (2)) (.leaf (5)))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (4)) (.leaf (3)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (2)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 42 (.leaf (7)) (.branch 43 (.leaf (0)) (.leaf (2))))) (.branch 47 (.branch 45 (.leaf (5)) (.branch 46 (.leaf (3)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (6))) (.branch 50 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_6120
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 29 (.leaf (5)) (.leaf (6))) (.branch 41 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-24))) (.branch 43 (.leaf (-34)) (.leaf (-40)))),
  (.branch 25 (.branch 2 (.leaf (0)) (.leaf (-27))) (.branch 29 (.leaf (-30)) (.leaf (-43)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-2))) (.branch 44 (.leaf (-4)) (.leaf (-8)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-14)) (.leaf (-16)))) (.branch 23 (.leaf (-21)) (.branch 30 (.leaf (-23)) (.leaf (-25))))),
  (.branch 11 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.branch 45 (.leaf (-6)) (.leaf (-7)))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 17 (.leaf (0)) (.branch 42 (.leaf (-17)) (.leaf (-18)))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-22)) (.leaf (-26))))]
  high := ![(.branch 49 (.branch 44 (.leaf (-40)) (.leaf (-36))) (.branch 50 (.leaf (-29)) (.leaf (-22)))),
  (.branch 42 (.branch 30 (.leaf (-43)) (.branch 36 (.leaf (-42)) (.leaf (-41)))) (.branch 49 (.branch 48 (.leaf (-40)) (.leaf (-33))) (.branch 50 (.leaf (-26)) (.leaf (-19))))),
  (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-5))) (.branch 47 (.leaf (-2)) (.leaf (0)))),
  (.branch 47 (.branch 31 (.leaf (-25)) (.branch 39 (.leaf (-24)) (.leaf (-23)))) (.branch 49 (.branch 48 (.leaf (-20)) (.leaf (-17))) (.branch 50 (.leaf (-14)) (.leaf (-11))))),
  (.branch 25 (.branch 12 (.leaf (-7)) (.leaf (-6))) (.branch 38 (.leaf (-5)) (.leaf (-4)))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.leaf (-4)) (.branch 50 (.leaf (-3)) (.leaf (-2))))),
  (.branch 50 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-16))) (.branch 45 (.leaf (-14)) (.leaf (-12)))) (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 39 (.branch 33 (.branch 30 (.branch 29 (.leaf (-26)) (.leaf (-25))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-23)) (.leaf (-22))))) (.branch 36 (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-20)) (.leaf (-19)))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-17)) (.leaf (-16)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10))))) (.branch 48 (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))))))]
def witnessP9_313_6121 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (8)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (5)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (7)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (2)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (6)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (5)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (8)) (.leaf (3))) (.branch 24 (.leaf (2)) (.leaf (0))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (4)) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 29 (.leaf (7)) (.branch 30 (.leaf (5)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (6)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (4)) (.leaf (0)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (8)) (.branch 40 (.leaf (5)) (.leaf (2)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (3)) (.leaf (1))))) (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (7)) (.leaf (4)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (2))) (.branch 50 (.leaf (5)) (.leaf (6))))))))
  code := certificateP9_6121
  counts := ![(.branch 25 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 31 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.leaf (15)))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 43 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-4)))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-36)) (.leaf (-37)))) (.branch 33 (.leaf (-38)) (.branch 43 (.leaf (-39)) (.leaf (-40))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (-21))) (.branch 26 (.leaf (-22)) (.leaf (-23)))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 49 (.leaf (-15)) (.branch 50 (.leaf (-10)) (.leaf (-5)))),
  (.branch 47 (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.leaf (-4)) (.leaf (-2))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-40)) (.leaf (-35))) (.branch 46 (.leaf (-30)) (.leaf (-25)))) (.branch 49 (.branch 48 (.leaf (-20)) (.leaf (-15))) (.branch 50 (.leaf (-10)) (.leaf (-5))))),
  (.branch 48 (.branch 27 (.leaf (-23)) (.leaf (-20))) (.branch 49 (.leaf (-15)) (.branch 50 (.leaf (-10)) (.leaf (-5))))),
  (.branch 10 (.leaf (-6)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_313_6122 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (6)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (4)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (5)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (1)) (.leaf (7))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (3)) (.leaf (4)))) (.branch 29 (.leaf (1)) (.branch 30 (.leaf (2)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (5)) (.branch 33 (.leaf (3)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (4))) (.branch 37 (.leaf (2)) (.leaf (6)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (3)) (.leaf (1)))) (.branch 42 (.leaf (4)) (.branch 43 (.leaf (0)) (.leaf (2))))) (.branch 47 (.branch 45 (.leaf (5)) (.branch 46 (.leaf (3)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (2))) (.branch 50 (.leaf (8)) (.leaf (4))))))))
  code := certificateP9_6122
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 29 (.leaf (5)) (.leaf (6))) (.branch 41 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))) (.branch 17 (.leaf (-12)) (.branch 34 (.leaf (-14)) (.leaf (-15))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-19))) (.branch 18 (.leaf (-22)) (.branch 29 (.leaf (-26)) (.leaf (-29))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 16 (.leaf (-14)) (.branch 49 (.leaf (-17)) (.leaf (-20))))),
  (.branch 33 (.branch 3 (.leaf (0)) (.leaf (-19))) (.branch 40 (.leaf (-23)) (.branch 46 (.leaf (-26)) (.leaf (-33))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (-2))) (.branch 28 (.leaf (-3)) (.branch 42 (.leaf (-4)) (.leaf (-6))))),
  (.branch 7 (.leaf (0)) (.branch 32 (.leaf (-23)) (.leaf (-25)))),
  (.branch 12 (.leaf (0)) (.leaf (-27))),
  (.branch 25 (.leaf (0)) (.leaf (-26))),
  (.branch 50 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 44 (.branch 35 (.leaf (-15)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-9)) (.leaf (-6))))),
  (.branch 42 (.branch 30 (.leaf (-29)) (.branch 36 (.leaf (-28)) (.leaf (-27)))) (.branch 49 (.branch 48 (.leaf (-26)) (.leaf (-21))) (.branch 50 (.leaf (-16)) (.leaf (-11))))),
  (.branch 50 (.leaf (-20)) (.leaf (-16))),
  (.branch 48 (.branch 47 (.leaf (-33)) (.leaf (-29))) (.branch 49 (.leaf (-25)) (.branch 50 (.leaf (-21)) (.leaf (-17))))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 47 (.branch 46 (.leaf (-3)) (.leaf (-2))) (.branch 48 (.leaf (-1)) (.leaf (0))))),
  (.branch 47 (.branch 33 (.leaf (-25)) (.branch 46 (.leaf (-24)) (.leaf (-20)))) (.branch 49 (.branch 48 (.leaf (-16)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4))))),
  (.branch 44 (.branch 40 (.branch 13 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-24)))) (.branch 42 (.branch 41 (.leaf (-22)) (.leaf (-20))) (.branch 43 (.leaf (-18)) (.leaf (-16))))) (.branch 47 (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (-26)) (.branch 27 (.leaf (-25)) (.leaf (-24)))) (.branch 29 (.leaf (-23)) (.branch 30 (.leaf (-22)) (.leaf (-21))))) (.branch 34 (.branch 32 (.leaf (-20)) (.branch 33 (.leaf (-19)) (.leaf (-18)))) (.branch 36 (.branch 35 (.leaf (-17)) (.leaf (-16))) (.branch 37 (.leaf (-15)) (.leaf (-14)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))) (.branch 42 (.leaf (-10)) (.branch 43 (.leaf (-9)) (.leaf (-8))))) (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_313_6123 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (6)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (7)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (5)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (3)) (.leaf (0)))) (.branch 16 (.leaf (8)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (5)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (1))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (7)) (.branch 27 (.leaf (0)) (.leaf (4)))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (1)) (.leaf (5))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (8)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (4)) (.leaf (2)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (6)) (.branch 40 (.leaf (0)) (.leaf (5)))) (.branch 42 (.leaf (1)) (.branch 43 (.leaf (7)) (.leaf (0))))) (.branch 47 (.branch 45 (.leaf (3)) (.branch 46 (.leaf (2)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (4)) (.leaf (0))) (.branch 50 (.leaf (8)) (.leaf (5))))))))
  code := certificateP9_6123
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 45 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 48 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 11 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 35 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-29))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (-13))) (.branch 37 (.leaf (-14)) (.leaf (-16)))),
  (.branch 20 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 9 (.leaf (0)) (.leaf (-8))),
  (.branch 16 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 45 (.branch 36 (.leaf (-12)) (.leaf (-11))) (.branch 50 (.leaf (-9)) (.leaf (-6)))),
  (.branch 49 (.branch 48 (.leaf (-12)) (.leaf (-9))) (.branch 50 (.leaf (-6)) (.leaf (-3)))),
  (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 35 (.branch 4 (.leaf (-29)) (.leaf (-28))) (.branch 46 (.leaf (-25)) (.leaf (-21)))) (.branch 49 (.branch 48 (.leaf (-17)) (.leaf (-13))) (.branch 50 (.leaf (-9)) (.leaf (-5))))),
  (.branch 49 (.branch 38 (.leaf (-16)) (.leaf (-13))) (.branch 50 (.leaf (-9)) (.leaf (-5)))),
  (.branch 21 (.leaf (-2)) (.leaf (0))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-8)) (.leaf (-7))) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessP9_313_6124 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (6)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (7)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (8)) (.leaf (1)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (6)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (7)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (5))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (8)) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (0)) (.leaf (6))))) (.branch 34 (.branch 32 (.leaf (4)) (.branch 33 (.leaf (1)) (.leaf (7)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (3)) (.leaf (5)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (8)) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 42 (.leaf (2)) (.branch 43 (.leaf (6)) (.leaf (4))))) (.branch 47 (.branch 45 (.leaf (3)) (.branch 46 (.leaf (1)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (7)) (.leaf (2))) (.branch 50 (.leaf (5)) (.leaf (8))))))))
  code := certificateP9_6124
  counts := ![(.branch 24 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 41 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 27 (.leaf (-24)) (.branch 33 (.leaf (-25)) (.leaf (-27))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-12))) (.branch 16 (.leaf (-14)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.branch 44 (.leaf (-27)) (.leaf (-28)))),
  (.branch 12 (.leaf (0)) (.branch 50 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-8)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.branch 34 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0))]
  high := ![(.branch 48 (.branch 36 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-6)) (.leaf (-3))))),
  (.branch 48 (.branch 34 (.leaf (-27)) (.branch 47 (.leaf (-26)) (.leaf (-21)))) (.branch 49 (.leaf (-16)) (.branch 50 (.leaf (-11)) (.leaf (-6))))),
  (.branch 30 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.branch 50 (.leaf (-11)) (.leaf (-6))))),
  (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 45 (.leaf (-28)) (.branch 46 (.leaf (-24)) (.leaf (-20)))) (.branch 49 (.branch 48 (.leaf (-16)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-4)),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.leaf (-2))))),
  (.branch 49 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (0))]
def witnessP9_313_6125 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (6)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (3)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (1)) (.leaf (4))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (3)) (.branch 27 (.leaf (0)) (.leaf (7)))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (1)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (5)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (2)) (.leaf (1)))) (.branch 42 (.leaf (4)) (.branch 43 (.leaf (3)) (.leaf (0))))) (.branch 47 (.branch 45 (.leaf (8)) (.branch 46 (.leaf (2)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (3))) (.branch 50 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_6125
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 41 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 46 (.leaf (7)) (.branch 51 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 43 (.leaf (7)) (.branch 49 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 11 (.leaf (0)) (.leaf (-40))),
  (.branch 28 (.leaf (0)) (.leaf (-23))),
  (.branch 45 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 49 (.branch 40 (.leaf (-14)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4)))),
  (.branch 48 (.branch 42 (.leaf (-13)) (.leaf (-12))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 44 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 50 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-2)),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))) (.branch 42 (.leaf (-10)) (.branch 43 (.leaf (-9)) (.leaf (-8))))) (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-40)) (.leaf (-39))) (.branch 14 (.leaf (-38)) (.branch 15 (.leaf (-37)) (.leaf (-36))))) (.branch 18 (.branch 17 (.leaf (-35)) (.leaf (-34))) (.branch 19 (.leaf (-33)) (.branch 20 (.leaf (-32)) (.leaf (-31)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-30)) (.leaf (-29))) (.branch 24 (.leaf (-28)) (.branch 25 (.leaf (-27)) (.leaf (-26))))) (.branch 28 (.branch 27 (.leaf (-25)) (.leaf (-24))) (.branch 29 (.leaf (-23)) (.branch 30 (.leaf (-22)) (.leaf (-21))))))) (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-20)) (.leaf (-19))) (.branch 34 (.leaf (-18)) (.branch 35 (.leaf (-17)) (.leaf (-16))))) (.branch 38 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 39 (.branch 33 (.branch 30 (.branch 29 (.leaf (-23)) (.leaf (-22))) (.branch 31 (.leaf (-21)) (.branch 32 (.leaf (-20)) (.leaf (-19))))) (.branch 36 (.branch 34 (.leaf (-18)) (.branch 35 (.leaf (-17)) (.leaf (-16)))) (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_313_6126 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (5)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (7)) (.leaf (4)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (3)) (.leaf (8)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (5)))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (7)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (8))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (4)) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 29 (.leaf (6)) (.branch 30 (.leaf (0)) (.leaf (2))))) (.branch 34 (.branch 32 (.leaf (5)) (.branch 33 (.leaf (7)) (.leaf (4)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (3)) (.leaf (8)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (5)) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 42 (.leaf (6)) (.branch 43 (.leaf (4)) (.leaf (1))))) (.branch 47 (.branch 45 (.leaf (3)) (.branch 46 (.leaf (7)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (2)) (.leaf (5))) (.branch 50 (.leaf (8)) (.leaf (4))))))))
  code := certificateP9_6126
  counts := ![(.branch 24 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 41 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 39 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-35)) (.leaf (-38)))),
  (.branch 8 (.leaf (0)) (.branch 33 (.leaf (-19)) (.leaf (-21)))),
  (.branch 12 (.leaf (0)) (.branch 50 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 48 (.branch 36 (.leaf (-14)) (.branch 42 (.leaf (-13)) (.leaf (-12)))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-6)) (.leaf (-3))))),
  (.branch 47 (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 40 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4)))),
  (.branch 45 (.branch 30 (.branch 17 (.leaf (-38)) (.leaf (-37))) (.branch 43 (.leaf (-36)) (.branch 44 (.leaf (-32)) (.leaf (-28))))) (.branch 48 (.branch 46 (.leaf (-24)) (.branch 47 (.leaf (-20)) (.leaf (-16)))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 48 (.branch 34 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-16)))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-4))]
def witnessP9_313_6127 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (1)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (4)) (.branch 14 (.leaf (3)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (5)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (7)) (.leaf (2))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (5)) (.leaf (1)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (4)) (.leaf (3))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (5)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (4)) (.leaf (0)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (3)) (.branch 40 (.leaf (0)) (.leaf (8)))) (.branch 42 (.leaf (2)) (.branch 43 (.leaf (0)) (.leaf (5))))) (.branch 47 (.branch 45 (.leaf (1)) (.branch 46 (.leaf (0)) (.leaf (4)))) (.branch 49 (.branch 48 (.leaf (3)) (.leaf (0))) (.branch 50 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6127
  counts := ![(.branch 23 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 38 (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 43 (.branch 40 (.leaf (14)) (.leaf (15))) (.branch 46 (.leaf (16)) (.branch 49 (.leaf (17)) (.leaf (18))))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 37 (.leaf (-7)) (.leaf (-8)))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-44))),
  (.branch 24 (.leaf (0)) (.leaf (-27))),
  (.branch 41 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 44 (.branch 41 (.leaf (-15)) (.leaf (-14))) (.branch 47 (.leaf (-13)) (.branch 50 (.leaf (-12)) (.leaf (-6))))),
  (.branch 47 (.branch 37 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 49 (.branch 40 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-5)) (.leaf (-4))))),
  (.branch 35 (.leaf (-2)) (.branch 45 (.leaf (-1)) (.leaf (0)))),
  (.branch 29 (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-44)) (.leaf (-43))) (.branch 10 (.leaf (-42)) (.branch 11 (.leaf (-41)) (.leaf (-40))))) (.branch 15 (.branch 13 (.leaf (-39)) (.branch 14 (.leaf (-38)) (.leaf (-37)))) (.branch 16 (.leaf (-36)) (.branch 17 (.leaf (-35)) (.leaf (-34)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-33)) (.leaf (-32))) (.branch 21 (.leaf (-31)) (.branch 22 (.leaf (-30)) (.leaf (-29))))) (.branch 26 (.branch 24 (.leaf (-28)) (.branch 25 (.leaf (-27)) (.leaf (-26)))) (.branch 27 (.leaf (-25)) (.branch 28 (.leaf (-24)) (.leaf (-23))))))) (.branch 40 (.branch 34 (.branch 31 (.branch 30 (.leaf (-22)) (.leaf (-21))) (.branch 32 (.leaf (-20)) (.branch 33 (.leaf (-19)) (.leaf (-18))))) (.branch 37 (.branch 35 (.leaf (-17)) (.branch 36 (.leaf (-16)) (.leaf (-15)))) (.branch 38 (.leaf (-14)) (.branch 39 (.leaf (-13)) (.leaf (-12)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 37 (.branch 30 (.branch 27 (.branch 25 (.leaf (-27)) (.branch 26 (.leaf (-26)) (.leaf (-25)))) (.branch 28 (.leaf (-24)) (.branch 29 (.leaf (-23)) (.leaf (-22))))) (.branch 33 (.branch 31 (.leaf (-21)) (.branch 32 (.leaf (-20)) (.leaf (-19)))) (.branch 35 (.branch 34 (.leaf (-18)) (.leaf (-17))) (.branch 36 (.leaf (-16)) (.leaf (-15)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (-14)) (.branch 39 (.leaf (-13)) (.leaf (-12)))) (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.leaf (-8))))) (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6))))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_313_6128 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (7)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (1)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (8)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (1)))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (3)) (.leaf (7))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (6)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (4))) (.branch 24 (.leaf (8)) (.leaf (3))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (5)) (.leaf (1)))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (7)) (.leaf (6))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (4)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (8))) (.branch 37 (.leaf (5)) (.leaf (2)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (6)) (.leaf (1)))) (.branch 42 (.leaf (3)) (.branch 43 (.leaf (7)) (.leaf (4))))) (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (2)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (5)) (.leaf (8))) (.branch 50 (.leaf (6)) (.leaf (3))))))))
  code := certificateP9_6128
  counts := ![(.branch 19 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 44 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 48 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.leaf (-27))) (.branch 13 (.leaf (-29)) (.branch 19 (.leaf (-31)) (.leaf (-33))))),
  (.branch 2 (.leaf (0)) (.leaf (-22))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (-22))) (.branch 33 (.leaf (-24)) (.leaf (-25)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (-13)) (.leaf (-14)))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (-1))) (.branch 40 (.leaf (-2)) (.branch 50 (.leaf (-4)) (.leaf (-5))))),
  (.branch 5 (.leaf (0)) (.branch 30 (.leaf (-31)) (.leaf (-33)))),
  (.branch 11 (.leaf (0)) (.branch 36 (.leaf (-7)) (.leaf (-9))))]
  high := ![(.branch 47 (.branch 33 (.branch 20 (.leaf (-33)) (.leaf (-32))) (.branch 46 (.leaf (-31)) (.leaf (-26)))) (.branch 49 (.branch 48 (.leaf (-21)) (.leaf (-16))) (.branch 50 (.leaf (-11)) (.leaf (-6))))),
  (.branch 48 (.branch 3 (.leaf (-22)) (.leaf (-21))) (.branch 49 (.leaf (-16)) (.branch 50 (.leaf (-11)) (.leaf (-6))))),
  (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 43 (.leaf (-1)) (.leaf (0))),
  (.branch 47 (.branch 45 (.branch 34 (.leaf (-25)) (.leaf (-23))) (.branch 46 (.leaf (-20)) (.leaf (-17)))) (.branch 49 (.branch 48 (.leaf (-14)) (.leaf (-11))) (.branch 50 (.leaf (-8)) (.leaf (-5))))),
  (.branch 38 (.branch 17 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-11)) (.branch 50 (.leaf (-8)) (.leaf (-5))))),
  (.leaf (-5)),
  (.branch 46 (.branch 44 (.branch 31 (.leaf (-33)) (.leaf (-32))) (.branch 45 (.leaf (-28)) (.leaf (-24)))) (.branch 48 (.branch 47 (.leaf (-20)) (.leaf (-16))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 37 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-4))))]
def witnessP9_313_6129 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (4)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (4)) (.leaf (8)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (3)) (.leaf (1))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (5)) (.branch 27 (.leaf (0)) (.leaf (4)))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (6)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (3)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (4)) (.leaf (7)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (2)) (.leaf (3)))) (.branch 42 (.leaf (1)) (.branch 43 (.leaf (5)) (.leaf (0))))) (.branch 47 (.branch 45 (.leaf (4)) (.branch 46 (.leaf (2)) (.leaf (8)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (0))) (.branch 50 (.leaf (3)) (.leaf (2))))))))
  code := certificateP9_6129
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 48 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 46 (.leaf (7)) (.branch 51 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))) (.branch 35 (.branch 22 (.leaf (-9)) (.leaf (-10))) (.branch 39 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 9 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.leaf (-43))),
  (.branch 13 (.leaf (0)) (.branch 38 (.leaf (-25)) (.leaf (-26)))),
  (.branch 21 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 45 (.branch 40 (.leaf (-12)) (.leaf (-11))) (.branch 50 (.leaf (-10)) (.leaf (-8)))),
  (.branch 43 (.branch 37 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 42 (.leaf (-3)) (.leaf (-2))),
  (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-8)) (.leaf (-7))) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 34 (.branch 31 (.branch 5 (.leaf (-43)) (.leaf (-42))) (.branch 32 (.leaf (-40)) (.branch 33 (.leaf (-38)) (.leaf (-36))))) (.branch 37 (.branch 35 (.leaf (-34)) (.branch 36 (.leaf (-32)) (.leaf (-30)))) (.branch 38 (.leaf (-28)) (.branch 39 (.leaf (-26)) (.leaf (-24)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-22)) (.leaf (-20))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-16)) (.leaf (-14))))) (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-26)) (.branch 40 (.leaf (-24)) (.leaf (-22)))) (.branch 42 (.leaf (-20)) (.branch 43 (.leaf (-18)) (.leaf (-16))))) (.branch 47 (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 48 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))))]
def witnessP9_313_6130 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (0)) (.leaf (7)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (5)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (8)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (2))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (1)) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 29 (.leaf (6)) (.branch 30 (.leaf (1)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (5)) (.branch 33 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (7)) (.leaf (0)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (4)) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 42 (.leaf (2)) (.branch 43 (.leaf (1)) (.leaf (3))))) (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (8)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (5))) (.branch 50 (.leaf (1)) (.leaf (2))))))))
  code := certificateP9_6130
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 31 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.leaf (15)))))),
  (.branch 26 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 33 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.leaf (15)))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 7 (.leaf (-14)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-45))),
  (.branch 12 (.leaf (0)) (.branch 37 (.leaf (-27)) (.leaf (-28)))),
  (.branch 20 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 49 (.branch 42 (.leaf (-16)) (.leaf (-15))) (.branch 50 (.leaf (-10)) (.leaf (-5)))),
  (.branch 37 (.leaf (-7)) (.branch 44 (.leaf (-6)) (.leaf (-5)))),
  (.branch 43 (.leaf (-1)) (.leaf (0))),
  (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.leaf (-2)) (.leaf (-1))),
  (.branch 39 (.branch 33 (.branch 30 (.branch 4 (.leaf (-45)) (.leaf (-44))) (.branch 31 (.leaf (-42)) (.branch 32 (.leaf (-40)) (.leaf (-38))))) (.branch 36 (.branch 34 (.leaf (-36)) (.branch 35 (.leaf (-34)) (.leaf (-32)))) (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-28)) (.leaf (-26)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-24)) (.branch 41 (.leaf (-22)) (.leaf (-20)))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-16)) (.leaf (-14))))) (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-28)) (.branch 39 (.leaf (-26)) (.leaf (-24)))) (.branch 42 (.branch 41 (.leaf (-22)) (.leaf (-20))) (.branch 43 (.leaf (-18)) (.leaf (-16))))) (.branch 47 (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 48 (.branch 21 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))))]
def witnessP9_313_6131 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (1)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (8)) (.branch 11 (.leaf (1)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (5)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (5))) (.branch 24 (.leaf (2)) (.leaf (0))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (3)) (.branch 27 (.leaf (6)) (.leaf (1)))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (0)) (.leaf (2))))) (.branch 34 (.branch 32 (.leaf (5)) (.branch 33 (.leaf (1)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (4))) (.branch 37 (.leaf (0)) (.leaf (2)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (5)) (.leaf (3)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (4)) (.leaf (7))))) (.branch 47 (.branch 45 (.leaf (1)) (.branch 46 (.leaf (2)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (3)) (.leaf (5))) (.branch 50 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_6131
  counts := ![(.branch 20 (.branch 8 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 25 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 45 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.leaf (7))))),
  (.branch 26 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.leaf (7))))),
  (.branch 29 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 20 (.leaf (-19)) (.branch 37 (.leaf (-24)) (.leaf (-29))))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-37))) (.branch 38 (.leaf (-39)) (.leaf (-40)))),
  (.branch 4 (.leaf (0)) (.leaf (-23))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (-2))) (.branch 21 (.leaf (-4)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 27 (.leaf (0)) (.leaf (-24))),
  (.branch 44 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-41)))]
  high := ![(.branch 48 (.branch 38 (.leaf (-29)) (.branch 43 (.leaf (-28)) (.leaf (-27)))) (.branch 49 (.leaf (-24)) (.branch 50 (.leaf (-21)) (.leaf (-18))))),
  (.leaf (-3)),
  (.branch 48 (.branch 39 (.leaf (-40)) (.branch 47 (.leaf (-35)) (.leaf (-28)))) (.branch 49 (.leaf (-21)) (.branch 50 (.leaf (-14)) (.leaf (-7))))),
  (.branch 27 (.branch 5 (.leaf (-23)) (.leaf (-22))) (.branch 49 (.leaf (-21)) (.branch 50 (.leaf (-14)) (.leaf (-7))))),
  (.branch 22 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (0)))),
  (.branch 41 (.leaf (-5)) (.branch 50 (.leaf (-4)) (.leaf (-2)))),
  (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (-24)) (.branch 29 (.leaf (-23)) (.leaf (-22)))) (.branch 31 (.leaf (-21)) (.branch 32 (.leaf (-20)) (.leaf (-19))))) (.branch 36 (.branch 34 (.leaf (-18)) (.branch 35 (.leaf (-17)) (.leaf (-16)))) (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 20 (.branch 15 (.branch 12 (.branch 11 (.leaf (-41)) (.leaf (-40))) (.branch 13 (.leaf (-39)) (.branch 14 (.leaf (-38)) (.leaf (-37))))) (.branch 17 (.branch 16 (.leaf (-36)) (.leaf (-35))) (.branch 18 (.leaf (-34)) (.branch 19 (.leaf (-33)) (.leaf (-32)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-31)) (.leaf (-30))) (.branch 23 (.leaf (-29)) (.branch 24 (.leaf (-28)) (.leaf (-27))))) (.branch 27 (.branch 26 (.leaf (-26)) (.leaf (-25))) (.branch 28 (.leaf (-24)) (.branch 29 (.leaf (-23)) (.leaf (-22))))))) (.branch 40 (.branch 35 (.branch 32 (.branch 31 (.leaf (-21)) (.leaf (-20))) (.branch 33 (.leaf (-19)) (.branch 34 (.leaf (-18)) (.leaf (-17))))) (.branch 37 (.branch 36 (.leaf (-16)) (.leaf (-15))) (.branch 38 (.leaf (-14)) (.branch 39 (.leaf (-13)) (.leaf (-12)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_313_6132 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (6)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (8)) (.leaf (1)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (4)) (.leaf (1)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (7)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (1)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (0))) (.branch 24 (.leaf (2)) (.leaf (8))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (1)) (.branch 27 (.leaf (3)) (.leaf (4)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (5)) (.leaf (2))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (3)) (.leaf (7)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (4))) (.branch 37 (.leaf (1)) (.leaf (2)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (6)) (.branch 40 (.leaf (0)) (.leaf (3)))) (.branch 42 (.leaf (8)) (.branch 43 (.leaf (1)) (.leaf (4))))) (.branch 47 (.branch 45 (.leaf (2)) (.branch 46 (.leaf (0)) (.leaf (5)))) (.branch 49 (.branch 48 (.leaf (3)) (.leaf (1))) (.branch 50 (.leaf (4)) (.leaf (7))))))))
  code := certificateP9_6132
  counts := ![(.branch 23 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 29 (.leaf (5)) (.leaf (6))) (.branch 40 (.leaf (7)) (.branch 46 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 43 (.leaf (7)) (.branch 49 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-14)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 38 (.leaf (-13)) (.branch 45 (.leaf (-14)) (.leaf (-15))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 33 (.leaf (-8)) (.leaf (-9)))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))) (.branch 28 (.leaf (-3)) (.branch 50 (.leaf (-4)) (.leaf (-5))))),
  (.branch 13 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 48 (.branch 41 (.leaf (-16)) (.branch 47 (.leaf (-15)) (.leaf (-12)))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-6)) (.leaf (-3))))),
  (.branch 44 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 50 (.leaf (-6)) (.leaf (-3)))),
  (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-13)) (.leaf (-11)))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-7)) (.leaf (-5))))),
  (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.leaf (-5)),
  (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 48 (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_313_6133 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (5)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (7)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (8)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (2)) (.leaf (5))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 29 (.leaf (6)) (.branch 30 (.leaf (1)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (2)) (.branch 33 (.leaf (4)) (.leaf (1)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (3)) (.leaf (7)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (0)) (.leaf (2)))) (.branch 42 (.leaf (5)) (.branch 43 (.leaf (1)) (.leaf (0))))) (.branch 47 (.branch 45 (.leaf (2)) (.branch 46 (.leaf (8)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (2))) (.branch 50 (.leaf (4)) (.leaf (1))))))))
  code := certificateP9_6133
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-43)) (.leaf (-44)))),
  (.branch 12 (.leaf (0)) (.leaf (-27))),
  (.branch 21 (.leaf (0)) (.branch 46 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 49 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 37 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-4)))),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-14)) (.branch 39 (.leaf (-13)) (.leaf (-12)))) (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.leaf (-8))))) (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 34 (.branch 31 (.branch 30 (.leaf (-44)) (.leaf (-42))) (.branch 32 (.leaf (-40)) (.branch 33 (.leaf (-38)) (.leaf (-36))))) (.branch 37 (.branch 35 (.leaf (-34)) (.branch 36 (.leaf (-32)) (.leaf (-30)))) (.branch 38 (.leaf (-28)) (.branch 39 (.leaf (-26)) (.leaf (-24)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-22)) (.leaf (-20))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-16)) (.leaf (-14))))) (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 44 (.branch 40 (.branch 13 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-24)))) (.branch 42 (.branch 41 (.leaf (-22)) (.leaf (-20))) (.branch 43 (.leaf (-18)) (.leaf (-16))))) (.branch 47 (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))))]
def witnessP9_313_6134 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (7)) (.leaf (0)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (2)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (3)))) (.branch 16 (.leaf (8)) (.branch 17 (.leaf (5)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (6)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (3)) (.leaf (7))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (5)) (.leaf (2)))) (.branch 29 (.leaf (1)) (.branch 30 (.leaf (0)) (.leaf (6))))) (.branch 34 (.branch 32 (.leaf (3)) (.branch 33 (.leaf (8)) (.leaf (4)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (5)) (.leaf (1)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (6)) (.leaf (3)))) (.branch 42 (.leaf (7)) (.branch 43 (.leaf (0)) (.leaf (4))))) (.branch 47 (.branch 45 (.leaf (2)) (.branch 46 (.leaf (1)) (.leaf (0)))) (.branch 49 (.branch 48 (.leaf (5)) (.leaf (3))) (.branch 50 (.leaf (8)) (.leaf (6))))))))
  code := certificateP9_6134
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 44 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 48 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 13 (.leaf (-15)) (.leaf (-16))))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-29)) (.leaf (-31)))),
  (.branch 6 (.leaf (0)) (.leaf (-17))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (-1))) (.branch 40 (.leaf (-2)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 16 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 49 (.branch 48 (.leaf (-16)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4)))),
  (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 37 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.leaf (-4)) (.leaf (-2))),
  (.branch 47 (.branch 45 (.branch 24 (.leaf (-31)) (.leaf (-29))) (.branch 46 (.leaf (-25)) (.leaf (-21)))) (.branch 49 (.branch 48 (.leaf (-17)) (.leaf (-13))) (.branch 50 (.leaf (-9)) (.leaf (-5))))),
  (.branch 38 (.branch 7 (.leaf (-17)) (.leaf (-16))) (.branch 49 (.leaf (-13)) (.branch 50 (.leaf (-9)) (.leaf (-5))))),
  (.branch 41 (.leaf (-4)) (.leaf (0))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_313_6135 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (7)) (.leaf (0)))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (1)) (.leaf (6)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (3)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (8)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (1)) (.leaf (7))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (3)) (.leaf (1)))) (.branch 29 (.leaf (6)) (.branch 30 (.leaf (2)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (4)) (.branch 33 (.leaf (1)) (.leaf (8)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (5))) (.branch 37 (.leaf (1)) (.leaf (2)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (3)) (.leaf (1)))) (.branch 42 (.leaf (7)) (.branch 43 (.leaf (0)) (.leaf (4))))) (.branch 47 (.branch 45 (.leaf (1)) (.branch 46 (.leaf (6)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (5))) (.branch 50 (.leaf (1)) (.leaf (8))))))))
  code := certificateP9_6135
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 27 (.leaf (-43)) (.leaf (-45)))),
  (.branch 6 (.leaf (0)) (.branch 44 (.leaf (-27)) (.leaf (-28)))),
  (.branch 10 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 49 (.branch 44 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4)))),
  (.branch 46 (.leaf (-7)) (.leaf (-4))),
  (.branch 48 (.branch 39 (.leaf (-9)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 45 (.branch 42 (.branch 28 (.leaf (-45)) (.branch 41 (.leaf (-44)) (.leaf (-40)))) (.branch 43 (.leaf (-36)) (.branch 44 (.leaf (-32)) (.leaf (-28))))) (.branch 48 (.branch 46 (.leaf (-24)) (.branch 47 (.leaf (-20)) (.leaf (-16)))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 47 (.branch 45 (.leaf (-28)) (.branch 46 (.leaf (-24)) (.leaf (-20)))) (.branch 49 (.branch 48 (.leaf (-16)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4))))),
  (.branch 24 (.branch 11 (.leaf (-11)) (.leaf (-10))) (.branch 37 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-4))))),
  (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_313_6136 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (2)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (1)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (2)) (.leaf (8)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (0)) (.leaf (4)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (5)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (7)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (4))) (.branch 24 (.leaf (2)) (.leaf (5))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (3)) (.leaf (1)))) (.branch 29 (.leaf (8)) (.branch 30 (.leaf (6)) (.leaf (2))))) (.branch 34 (.branch 32 (.leaf (4)) (.branch 33 (.leaf (0)) (.leaf (5)))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (3))) (.branch 37 (.leaf (2)) (.leaf (7)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (4)) (.leaf (1)))) (.branch 42 (.leaf (5)) (.branch 43 (.leaf (2)) (.leaf (3))))) (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (8)) (.leaf (6)))) (.branch 49 (.branch 48 (.leaf (1)) (.leaf (4))) (.branch 50 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6136
  counts := ![(.branch 20 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.leaf (-43))) (.branch 26 (.leaf (-46)) (.branch 45 (.leaf (-47)) (.leaf (-48))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-27))) (.branch 28 (.leaf (-30)) (.leaf (-31)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 48 (.branch 46 (.leaf (-48)) (.branch 47 (.leaf (-40)) (.leaf (-32)))) (.branch 49 (.leaf (-24)) (.branch 50 (.leaf (-16)) (.leaf (-8))))),
  (.branch 42 (.branch 29 (.leaf (-31)) (.leaf (-29))) (.branch 49 (.leaf (-24)) (.branch 50 (.leaf (-16)) (.leaf (-8))))),
  (.branch 12 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-8)))),
  (.branch 47 (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 41 (.leaf (-5)) (.branch 50 (.leaf (-4)) (.leaf (-2)))),
  (.branch 43 (.leaf (-1)) (.leaf (0))),
  (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1)))),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))) (.branch 42 (.leaf (-10)) (.branch 43 (.leaf (-9)) (.leaf (-8))))) (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_313_6137 : CycleWitness 9 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (3)) (.leaf (7)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (4)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (5)) (.leaf (8)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (2))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 29 (.leaf (6)) (.branch 30 (.leaf (1)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (4)) (.branch 33 (.leaf (2)) (.leaf (1)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (3))) (.branch 37 (.leaf (5)) (.leaf (7)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (0)) (.leaf (4)))) (.branch 42 (.leaf (2)) (.branch 43 (.leaf (1)) (.leaf (0))))) (.branch 47 (.branch 45 (.leaf (3)) (.branch 46 (.leaf (8)) (.leaf (1)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (4))) (.branch 50 (.leaf (2)) (.leaf (1))))))))
  code := certificateP9_6137
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-43)) (.leaf (-44)))),
  (.branch 12 (.leaf (0)) (.leaf (-27))),
  (.branch 21 (.leaf (0)) (.branch 46 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 49 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.leaf (-2)),
  (.branch 47 (.branch 37 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.leaf (-4)) (.leaf (-2))),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-14)) (.branch 39 (.leaf (-13)) (.leaf (-12)))) (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.leaf (-8))))) (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 49 (.branch 48 (.leaf (-4)) (.leaf (-3))) (.branch 50 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 34 (.branch 31 (.branch 30 (.leaf (-44)) (.leaf (-42))) (.branch 32 (.leaf (-40)) (.branch 33 (.leaf (-38)) (.leaf (-36))))) (.branch 37 (.branch 35 (.leaf (-34)) (.branch 36 (.leaf (-32)) (.leaf (-30)))) (.branch 38 (.leaf (-28)) (.branch 39 (.leaf (-26)) (.leaf (-24)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-22)) (.leaf (-20))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-16)) (.leaf (-14))))) (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-10)) (.leaf (-8)))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 44 (.branch 40 (.branch 13 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-24)))) (.branch 42 (.branch 41 (.leaf (-22)) (.leaf (-20))) (.branch 43 (.leaf (-18)) (.leaf (-16))))) (.branch 47 (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 49 (.branch 48 (.leaf (-8)) (.leaf (-6))) (.branch 50 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2)))))]
def witnessP9_313_6138 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (7)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (2)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (4)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (5)) (.leaf (3)))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))))) (.branch 38 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (4)) (.leaf (3)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (8)) (.branch 34 (.leaf (0)) (.leaf (1)))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (3)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (4)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (2)) (.leaf (0))))) (.branch 47 (.branch 45 (.leaf (1)) (.branch 46 (.leaf (6)) (.leaf (3)))) (.branch 48 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2))))))))
  code := certificateP9_6138
  counts := ![(.branch 23 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))) (.branch 36 (.branch 27 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.branch 34 (.leaf (12)) (.leaf (13))))) (.branch 42 (.branch 39 (.leaf (14)) (.leaf (15))) (.branch 44 (.leaf (16)) (.branch 48 (.leaf (17)) (.leaf (18))))))),
  (.branch 24 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 46 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 19 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))) (.branch 27 (.leaf (-5)) (.branch 44 (.leaf (-6)) (.leaf (-7))))),
  (.branch 24 (.leaf (0)) (.leaf (-1))),
  (.branch 18 (.branch 12 (.leaf (0)) (.leaf (-2))) (.branch 37 (.leaf (-3)) (.branch 43 (.leaf (-4)) (.leaf (-5))))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 21 (.leaf (0)) (.leaf (-29))),
  (.branch 46 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-42))),
  (.branch 33 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 45 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))),
  (.leaf (-1)),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-3))) (.branch 46 (.leaf (-1)) (.leaf (0)))),
  (.branch 39 (.branch 30 (.leaf (-10)) (.leaf (-9))) (.branch 48 (.leaf (-8)) (.branch 49 (.leaf (-6)) (.leaf (-4))))),
  (.branch 45 (.branch 42 (.branch 29 (.leaf (-19)) (.leaf (-18))) (.branch 43 (.leaf (-16)) (.branch 44 (.leaf (-14)) (.leaf (-12))))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 35 (.branch 28 (.branch 24 (.branch 22 (.leaf (-29)) (.branch 23 (.leaf (-28)) (.leaf (-27)))) (.branch 26 (.branch 25 (.leaf (-26)) (.leaf (-25))) (.branch 27 (.leaf (-24)) (.leaf (-23))))) (.branch 31 (.branch 29 (.leaf (-22)) (.branch 30 (.leaf (-21)) (.leaf (-20)))) (.branch 33 (.branch 32 (.leaf (-19)) (.leaf (-18))) (.branch 34 (.leaf (-17)) (.leaf (-16)))))) (.branch 42 (.branch 38 (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-14)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-12)) (.leaf (-11))) (.branch 41 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-42)) (.leaf (-41))) (.branch 11 (.leaf (-40)) (.branch 12 (.leaf (-39)) (.leaf (-38))))) (.branch 15 (.branch 14 (.leaf (-37)) (.leaf (-36))) (.branch 16 (.leaf (-35)) (.branch 17 (.leaf (-34)) (.leaf (-33)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-32)) (.leaf (-31))) (.branch 21 (.leaf (-30)) (.branch 22 (.leaf (-29)) (.leaf (-28))))) (.branch 26 (.branch 24 (.leaf (-27)) (.branch 25 (.leaf (-26)) (.leaf (-25)))) (.branch 27 (.leaf (-24)) (.branch 28 (.leaf (-23)) (.leaf (-22))))))) (.branch 39 (.branch 34 (.branch 31 (.branch 30 (.leaf (-21)) (.leaf (-20))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-18)) (.leaf (-17))))) (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (-17)) (.leaf (-16))) (.branch 36 (.leaf (-15)) (.leaf (-14)))) (.branch 39 (.branch 38 (.leaf (-13)) (.leaf (-12))) (.branch 40 (.leaf (-11)) (.leaf (-10))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 44 (.leaf (-7)) (.leaf (-6)))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_313_6139 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (7)) (.leaf (5)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (3)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (8)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (2)) (.leaf (5)))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (3))))))) (.branch 38 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (7)) (.leaf (6)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (4))))) (.branch 35 (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (1)))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (5)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (8)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (4)) (.leaf (0))))) (.branch 47 (.branch 45 (.leaf (1)) (.branch 46 (.leaf (2)) (.leaf (6)))) (.branch 48 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_6139
  counts := ![(.branch 23 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))) (.branch 36 (.branch 27 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.branch 34 (.leaf (12)) (.leaf (13))))) (.branch 42 (.branch 39 (.leaf (14)) (.leaf (15))) (.branch 44 (.leaf (16)) (.branch 48 (.leaf (17)) (.leaf (18))))))),
  (.branch 24 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 19 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))) (.branch 27 (.leaf (-5)) (.branch 44 (.leaf (-6)) (.leaf (-7))))),
  (.branch 24 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (-6))) (.branch 43 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 13 (.leaf (0)) (.branch 29 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-22))),
  (.branch 16 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 45 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))),
  (.leaf (-1)),
  (.branch 47 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 38 (.leaf (-1)) (.leaf (0))),
  (.branch 46 (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7)))) (.branch 48 (.branch 47 (.leaf (-6)) (.leaf (-5))) (.branch 49 (.leaf (-4)) (.leaf (-3))))),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))) (.branch 42 (.leaf (-10)) (.branch 43 (.leaf (-9)) (.leaf (-8))))) (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 48 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.leaf (-2)))),
  (.branch 39 (.branch 33 (.branch 30 (.branch 29 (.leaf (-22)) (.leaf (-21))) (.branch 31 (.leaf (-20)) (.branch 32 (.leaf (-19)) (.leaf (-18))))) (.branch 36 (.branch 34 (.leaf (-17)) (.branch 35 (.leaf (-16)) (.leaf (-15)))) (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 43 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 44 (.leaf (-7)) (.leaf (-6)))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_313_6140 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (7)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (3)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (5)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (6)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.leaf (4))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (1)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (3)) (.branch 33 (.leaf (2)) (.leaf (8)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (4)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (2)) (.branch 39 (.leaf (0)) (.leaf (3)))) (.branch 41 (.leaf (1)) (.branch 42 (.leaf (5)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (6)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (3))) (.branch 49 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_6140
  counts := ![(.branch 22 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))) (.branch 35 (.branch 28 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 31 (.leaf (9)) (.leaf (10)))) (.branch 43 (.branch 39 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 24 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 41 (.leaf (7)) (.branch 46 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 49 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-14)) (.leaf (-23)))) (.branch 28 (.leaf (-27)) (.branch 31 (.leaf (-31)) (.leaf (-35))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-25))) (.branch 24 (.leaf (-26)) (.branch 46 (.leaf (-27)) (.leaf (-29))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 21 (.leaf (-5)) (.leaf (-9)))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (-4))) (.branch 23 (.leaf (-5)) (.leaf (-6)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 20 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-41))),
  (.branch 34 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 40 (.branch 32 (.leaf (-35)) (.branch 36 (.leaf (-34)) (.leaf (-33)))) (.branch 48 (.branch 44 (.leaf (-32)) (.leaf (-31))) (.branch 49 (.leaf (-26)) (.leaf (-21))))),
  (.branch 48 (.branch 47 (.leaf (-29)) (.leaf (-22))) (.branch 49 (.leaf (-15)) (.leaf (-8)))),
  (.branch 22 (.leaf (-9)) (.leaf (-8))),
  (.branch 49 (.leaf (-6)) (.leaf (-3))),
  (.branch 38 (.leaf (-1)) (.leaf (0))),
  (.branch 45 (.branch 43 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-14)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-41)) (.leaf (-40))) (.branch 12 (.leaf (-39)) (.branch 13 (.leaf (-38)) (.leaf (-37))))) (.branch 16 (.branch 15 (.leaf (-36)) (.leaf (-35))) (.branch 17 (.leaf (-34)) (.branch 18 (.leaf (-33)) (.leaf (-32)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-31)) (.leaf (-30))) (.branch 22 (.leaf (-29)) (.branch 23 (.leaf (-28)) (.leaf (-27))))) (.branch 26 (.branch 25 (.leaf (-26)) (.leaf (-25))) (.branch 27 (.leaf (-24)) (.branch 28 (.leaf (-23)) (.leaf (-22))))))) (.branch 39 (.branch 34 (.branch 31 (.branch 30 (.leaf (-21)) (.leaf (-20))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-18)) (.leaf (-17))))) (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-12)) (.leaf (-11))) (.branch 41 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_313_6141 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (6)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (5)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (0))) (.branch 24 (.leaf (7)) (.leaf (1))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (5))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (3)) (.leaf (1)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (6)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (1)) (.branch 39 (.leaf (4)) (.leaf (0)))) (.branch 41 (.leaf (2)) (.branch 42 (.leaf (1)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (3)) (.branch 45 (.leaf (0)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (5)) (.leaf (0))) (.branch 49 (.leaf (8)) (.leaf (1))))))))
  code := certificateP9_6141
  counts := ![(.branch 23 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))) (.branch 37 (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 43 (.branch 40 (.leaf (14)) (.leaf (15))) (.branch 45 (.leaf (16)) (.branch 48 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 46 (.branch 42 (.leaf (11)) (.leaf (12))) (.branch 50 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 20 (.leaf (-10)) (.branch 45 (.leaf (-12)) (.leaf (-13))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 27 (.leaf (-13)) (.branch 30 (.leaf (-17)) (.leaf (-21))))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (-5))) (.branch 44 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (-32)) (.leaf (-34)))),
  (.branch 14 (.leaf (0)) (.branch 47 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.leaf (-14))),
  (.branch 24 (.leaf (0)) (.leaf (-26))),
  (.branch 49 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 46 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 43 (.branch 35 (.branch 31 (.leaf (-21)) (.leaf (-20))) (.branch 39 (.leaf (-19)) (.leaf (-18)))) (.branch 48 (.branch 47 (.leaf (-17)) (.leaf (-12))) (.branch 49 (.leaf (-7)) (.leaf (-2))))),
  (.branch 45 (.branch 42 (.branch 29 (.leaf (-19)) (.leaf (-18))) (.branch 43 (.leaf (-16)) (.branch 44 (.leaf (-14)) (.leaf (-12))))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 47 (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.leaf (-5)) (.branch 49 (.leaf (-4)) (.leaf (-3))))),
  (.branch 44 (.branch 41 (.branch 23 (.leaf (-34)) (.branch 40 (.leaf (-33)) (.leaf (-30)))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-24)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))),
  (.branch 43 (.branch 39 (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))) (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.leaf (-8))))) (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 30 (.branch 27 (.branch 25 (.leaf (-26)) (.branch 26 (.leaf (-25)) (.leaf (-24)))) (.branch 28 (.leaf (-23)) (.branch 29 (.leaf (-22)) (.leaf (-21))))) (.branch 33 (.branch 31 (.leaf (-20)) (.branch 32 (.leaf (-19)) (.leaf (-18)))) (.branch 35 (.branch 34 (.leaf (-17)) (.leaf (-16))) (.branch 36 (.leaf (-15)) (.leaf (-14)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-12)) (.leaf (-11)))) (.branch 41 (.leaf (-10)) (.branch 42 (.leaf (-9)) (.leaf (-8))))) (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_313_6142 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (7)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (1)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (4))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (3)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (8)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (1)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (3)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (2)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (6)) (.leaf (1))) (.branch 49 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_6142
  counts := ![(.branch 24 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 38 (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 43 (.branch 41 (.leaf (14)) (.leaf (15))) (.branch 46 (.leaf (16)) (.branch 49 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 8 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 31 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 48 (.leaf (13)) (.leaf (14)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 26 (.leaf (-9)) (.leaf (-10)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-17)))) (.branch 33 (.leaf (-21)) (.branch 36 (.leaf (-25)) (.leaf (-29))))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-15)) (.leaf (-16)))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 22 (.leaf (0)) (.leaf (-28))),
  (.branch 47 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-41))),
  (.branch 34 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 44 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.leaf (-7)))),
  (.branch 41 (.branch 37 (.leaf (-29)) (.leaf (-28))) (.branch 45 (.leaf (-27)) (.branch 49 (.leaf (-26)) (.leaf (-21))))),
  (.branch 47 (.branch 29 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-16)) (.leaf (-14))) (.branch 45 (.leaf (-12)) (.leaf (-10)))) (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-6))) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 36 (.branch 29 (.branch 25 (.branch 23 (.leaf (-28)) (.branch 24 (.leaf (-27)) (.leaf (-26)))) (.branch 27 (.branch 26 (.leaf (-25)) (.leaf (-24))) (.branch 28 (.leaf (-23)) (.leaf (-22))))) (.branch 32 (.branch 30 (.leaf (-21)) (.branch 31 (.leaf (-20)) (.leaf (-19)))) (.branch 34 (.branch 33 (.leaf (-18)) (.leaf (-17))) (.branch 35 (.leaf (-16)) (.leaf (-15)))))) (.branch 43 (.branch 39 (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))) (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.leaf (-8))))) (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-41)) (.leaf (-40))) (.branch 12 (.leaf (-39)) (.branch 13 (.leaf (-38)) (.leaf (-37))))) (.branch 16 (.branch 15 (.leaf (-36)) (.leaf (-35))) (.branch 17 (.leaf (-34)) (.branch 18 (.leaf (-33)) (.leaf (-32)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-31)) (.leaf (-30))) (.branch 22 (.leaf (-29)) (.branch 23 (.leaf (-28)) (.leaf (-27))))) (.branch 26 (.branch 25 (.leaf (-26)) (.leaf (-25))) (.branch 27 (.leaf (-24)) (.branch 28 (.leaf (-23)) (.leaf (-22))))))) (.branch 39 (.branch 34 (.branch 31 (.branch 30 (.leaf (-21)) (.leaf (-20))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-18)) (.leaf (-17))))) (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-12)) (.leaf (-11))) (.branch 41 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_313_6143 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (7)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (1)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (6))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (3)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (8)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (5)) (.leaf (1)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (3)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (2)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (4)) (.leaf (1))) (.branch 49 (.leaf (0)) (.leaf (6))))))))
  code := certificateP9_6143
  counts := ![(.branch 24 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 38 (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 43 (.branch 41 (.leaf (14)) (.leaf (15))) (.branch 46 (.leaf (16)) (.branch 49 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 8 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 31 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 48 (.leaf (13)) (.leaf (14)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 26 (.leaf (-9)) (.leaf (-10)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-17)))) (.branch 33 (.leaf (-21)) (.branch 36 (.leaf (-25)) (.leaf (-29))))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-15)) (.leaf (-16)))),
  (.branch 22 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-41))),
  (.branch 34 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 44 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.leaf (-7)))),
  (.branch 41 (.branch 37 (.leaf (-29)) (.leaf (-28))) (.branch 45 (.leaf (-27)) (.branch 49 (.leaf (-26)) (.leaf (-21))))),
  (.branch 47 (.branch 29 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-16)) (.leaf (-14))) (.branch 45 (.leaf (-12)) (.leaf (-10)))) (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-6))) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))),
  (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 29 (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-41)) (.leaf (-40))) (.branch 12 (.leaf (-39)) (.branch 13 (.leaf (-38)) (.leaf (-37))))) (.branch 16 (.branch 15 (.leaf (-36)) (.leaf (-35))) (.branch 17 (.leaf (-34)) (.branch 18 (.leaf (-33)) (.leaf (-32)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-31)) (.leaf (-30))) (.branch 22 (.leaf (-29)) (.branch 23 (.leaf (-28)) (.leaf (-27))))) (.branch 26 (.branch 25 (.leaf (-26)) (.leaf (-25))) (.branch 27 (.leaf (-24)) (.branch 28 (.leaf (-23)) (.leaf (-22))))))) (.branch 39 (.branch 34 (.branch 31 (.branch 30 (.leaf (-21)) (.leaf (-20))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-18)) (.leaf (-17))))) (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-12)) (.leaf (-11))) (.branch 41 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_313_6144 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (4)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (8)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (5)) (.leaf (7))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (3)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (6)) (.leaf (4)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (2)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (8)) (.branch 39 (.leaf (1)) (.leaf (0)))) (.branch 41 (.leaf (5)) (.branch 42 (.leaf (3)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (2)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (6)) (.leaf (7))))))))
  code := certificateP9_6144
  counts := ![(.branch 22 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 29 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 32 (.leaf (9)) (.leaf (10)))) (.branch 43 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 7 (.leaf (-16)) (.branch 32 (.leaf (-19)) (.leaf (-20))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 10 (.leaf (-14)) (.branch 14 (.leaf (-15)) (.leaf (-16))))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-15)) (.leaf (-16)))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (-26)) (.leaf (-28)))),
  (.branch 16 (.leaf (0)) (.branch 49 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 44 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-7))))),
  (.branch 40 (.leaf (-16)) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 47 (.branch 29 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-16)) (.leaf (-14))) (.branch 45 (.leaf (-12)) (.leaf (-10)))) (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-6))) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-6))) (.branch 49 (.leaf (-4)) (.leaf (-2)))),
  (.branch 45 (.branch 42 (.branch 25 (.leaf (-28)) (.leaf (-27))) (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-21)) (.leaf (-18))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-12))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (-3)),
  (.leaf (0)),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-12)) (.branch 40 (.leaf (-11)) (.leaf (-10)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_313_6145 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (8)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (7)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (2))) (.branch 24 (.leaf (1)) (.leaf (0))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (5)) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (2)) (.leaf (0)))) (.branch 35 (.leaf (8)) (.branch 36 (.leaf (1)) (.leaf (7)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (1)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (4)) (.leaf (2))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (0)) (.leaf (6)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6145
  counts := ![(.branch 25 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.leaf (15)))))),
  (.branch 24 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 28 (.leaf (7)) (.branch 32 (.leaf (8)) (.leaf (9)))) (.branch 44 (.branch 40 (.leaf (10)) (.leaf (11))) (.branch 48 (.leaf (12)) (.leaf (13)))))),
  (.branch 23 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 29 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 5 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 27 (.leaf (-14)) (.branch 47 (.leaf (-18)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 12 (.leaf (-23)) (.leaf (-44)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-20))),
  (.branch 17 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 22 (.leaf (0)) (.branch 46 (.leaf (-3)) (.leaf (-4)))),
  (.branch 14 (.leaf (0)) (.branch 37 (.leaf (-12)) (.leaf (-15)))),
  (.branch 7 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 48 (.leaf (-20)) (.branch 49 (.leaf (-15)) (.leaf (-10)))),
  (.branch 29 (.branch 17 (.branch 13 (.leaf (-44)) (.leaf (-43))) (.branch 21 (.leaf (-42)) (.branch 25 (.leaf (-41)) (.leaf (-40))))) (.branch 41 (.branch 33 (.leaf (-39)) (.branch 37 (.leaf (-38)) (.leaf (-37)))) (.branch 45 (.leaf (-36)) (.branch 49 (.leaf (-35)) (.leaf (-23)))))),
  (.branch 44 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.branch 35 (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-19))) (.branch 33 (.leaf (-18)) (.branch 34 (.leaf (-17)) (.leaf (-16))))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-14))) (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-12)) (.leaf (-11)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-8)) (.branch 44 (.leaf (-7)) (.leaf (-6))))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))),
  (.branch 43 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 46 (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7)))) (.branch 48 (.branch 47 (.leaf (-6)) (.leaf (-5))) (.branch 49 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 42 (.branch 38 (.branch 36 (.branch 8 (.leaf (-20)) (.leaf (-19))) (.branch 37 (.leaf (-18)) (.leaf (-17)))) (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-14)) (.leaf (-13))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.leaf (-9)))) (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5))))))]
def witnessP9_313_6146 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (3)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (4)) (.leaf (7))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (4)) (.branch 33 (.leaf (0)) (.leaf (2)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (3)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (6)) (.branch 39 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (4)) (.leaf (1))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (3)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (4)) (.leaf (8))))))))
  code := certificateP9_6146
  counts := ![(.branch 22 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 22 (.leaf (-14)) (.branch 47 (.leaf (-16)) (.leaf (-17))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))) (.branch 14 (.leaf (-15)) (.branch 18 (.leaf (-16)) (.leaf (-17))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-14)) (.branch 21 (.leaf (-15)) (.leaf (-16))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-9))) (.branch 36 (.leaf (-12)) (.leaf (-13)))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (-2))) (.branch 32 (.leaf (-3)) (.branch 49 (.leaf (-4)) (.leaf (-5))))),
  (.branch 13 (.leaf (0)) (.leaf (-37))),
  (.branch 38 (.leaf (0)) (.leaf (-12))),
  (.branch 25 (.leaf (0)) (.leaf (-25))),
  (.leaf (0))]
  high := ![(.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 44 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-12))) (.branch 49 (.leaf (-8)) (.leaf (-4)))),
  (.branch 47 (.branch 37 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 48 (.leaf (-8)) (.branch 49 (.leaf (-6)) (.leaf (-4))))),
  (.leaf (-5)),
  (.branch 31 (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-37)) (.leaf (-36))) (.branch 16 (.leaf (-35)) (.leaf (-34)))) (.branch 19 (.branch 18 (.leaf (-33)) (.leaf (-32))) (.branch 20 (.leaf (-31)) (.branch 21 (.leaf (-30)) (.leaf (-29)))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (-28)) (.leaf (-27))) (.branch 25 (.leaf (-26)) (.leaf (-25)))) (.branch 28 (.branch 27 (.leaf (-24)) (.leaf (-23))) (.branch 29 (.leaf (-22)) (.branch 30 (.leaf (-21)) (.leaf (-20))))))) (.branch 40 (.branch 35 (.branch 33 (.branch 32 (.leaf (-19)) (.leaf (-18))) (.branch 34 (.leaf (-17)) (.leaf (-16)))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-14))) (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-12)) (.leaf (-11)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-8)) (.branch 44 (.leaf (-7)) (.leaf (-6))))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-12)) (.branch 40 (.leaf (-11)) (.leaf (-10)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (-25)) (.branch 27 (.leaf (-24)) (.leaf (-23)))) (.branch 29 (.leaf (-22)) (.branch 30 (.leaf (-21)) (.leaf (-20))))) (.branch 34 (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-18)) (.leaf (-17)))) (.branch 35 (.leaf (-16)) (.branch 36 (.leaf (-15)) (.leaf (-14)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-12)) (.leaf (-11)))) (.branch 41 (.leaf (-10)) (.branch 42 (.leaf (-9)) (.leaf (-8))))) (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_313_6147 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (4)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (6)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (5)) (.leaf (8))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (6)) (.branch 33 (.leaf (0)) (.leaf (2)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (3)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (7)) (.branch 39 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (5)) (.leaf (1))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (4)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (6)) (.leaf (8))))))))
  code := certificateP9_6147
  counts := ![(.branch 22 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 22 (.leaf (-14)) (.branch 47 (.leaf (-16)) (.leaf (-17))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))) (.branch 14 (.leaf (-15)) (.branch 18 (.leaf (-16)) (.leaf (-17))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-14)) (.branch 21 (.leaf (-15)) (.leaf (-16))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 36 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 32 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 44 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-12))) (.branch 49 (.leaf (-8)) (.leaf (-4)))),
  (.branch 43 (.branch 39 (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))) (.branch 41 (.branch 40 (.leaf (-12)) (.leaf (-11))) (.branch 42 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 47 (.branch 46 (.leaf (-6)) (.leaf (-5))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2))))),
  (.branch 45 (.branch 43 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.leaf (-7)))) (.branch 47 (.branch 46 (.leaf (-6)) (.leaf (-5))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2)))))),
  (.leaf (-2)),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-12)) (.branch 40 (.leaf (-11)) (.leaf (-10)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_313_6148 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (8)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (7)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (1)) (.leaf (8))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (6)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (7)) (.leaf (2)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (3)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (5)) (.branch 39 (.leaf (0)) (.leaf (1)))) (.branch 41 (.leaf (2)) (.branch 42 (.leaf (8)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (4)) (.leaf (6)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (1)) (.leaf (7))))))))
  code := certificateP9_6148
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 26 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.branch 27 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-13)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-38)) (.leaf (-40)))),
  (.branch 12 (.leaf (0)) (.branch 45 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (-35)) (.leaf (-37)))),
  (.branch 13 (.leaf (0)) (.branch 46 (.leaf (-11)) (.leaf (-12)))),
  (.branch 33 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-26)))]
  high := ![(.branch 44 (.branch 27 (.leaf (-17)) (.leaf (-16))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 28 (.leaf (-12)) (.branch 45 (.leaf (-11)) (.leaf (-7)))),
  (.branch 48 (.branch 35 (.leaf (-14)) (.leaf (-12))) (.branch 49 (.leaf (-8)) (.leaf (-4)))),
  (.branch 43 (.branch 39 (.branch 21 (.leaf (-40)) (.branch 38 (.leaf (-39)) (.leaf (-36)))) (.branch 41 (.branch 40 (.leaf (-33)) (.leaf (-30))) (.branch 42 (.leaf (-27)) (.leaf (-24))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-18)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-12))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 43 (.branch 40 (.branch 22 (.leaf (-37)) (.branch 39 (.leaf (-36)) (.leaf (-33)))) (.branch 41 (.leaf (-30)) (.branch 42 (.leaf (-27)) (.leaf (-24))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-18)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3)))),
  (.branch 34 (.leaf (-1)) (.leaf (0))),
  (.branch 45 (.branch 26 (.branch 9 (.leaf (-26)) (.leaf (-25))) (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-21)) (.leaf (-18))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-12))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))))]
def witnessP9_313_6149 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (5)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (4)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (3)) (.leaf (6))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (3)) (.branch 33 (.leaf (0)) (.leaf (2)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (4)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (8)) (.branch 39 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (3)) (.leaf (1))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (5)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (3)) (.leaf (6))))))))
  code := certificateP9_6149
  counts := ![(.branch 22 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 22 (.leaf (-14)) (.branch 47 (.leaf (-16)) (.leaf (-17))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))) (.branch 14 (.leaf (-15)) (.branch 18 (.leaf (-16)) (.leaf (-17))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-14)) (.branch 21 (.leaf (-15)) (.leaf (-16))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (-2))) (.branch 32 (.leaf (-3)) (.branch 49 (.leaf (-4)) (.leaf (-5))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 36 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-37))),
  (.branch 38 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 44 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-12))) (.branch 49 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-5)),
  (.branch 43 (.branch 39 (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))) (.branch 41 (.branch 40 (.leaf (-12)) (.leaf (-11))) (.branch 42 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 47 (.branch 46 (.leaf (-6)) (.leaf (-5))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 31 (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-37)) (.leaf (-36))) (.branch 16 (.leaf (-35)) (.leaf (-34)))) (.branch 19 (.branch 18 (.leaf (-33)) (.leaf (-32))) (.branch 20 (.leaf (-31)) (.branch 21 (.leaf (-30)) (.leaf (-29)))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (-28)) (.leaf (-27))) (.branch 25 (.leaf (-26)) (.leaf (-25)))) (.branch 28 (.branch 27 (.leaf (-24)) (.leaf (-23))) (.branch 29 (.leaf (-22)) (.branch 30 (.leaf (-21)) (.leaf (-20))))))) (.branch 40 (.branch 35 (.branch 33 (.branch 32 (.leaf (-19)) (.leaf (-18))) (.branch 34 (.leaf (-17)) (.leaf (-16)))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-14))) (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-12)) (.leaf (-11)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-8)) (.branch 44 (.leaf (-7)) (.leaf (-6))))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-12)) (.branch 40 (.leaf (-11)) (.leaf (-10)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_313_6150 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (2)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (1)) (.leaf (3))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (0)) (.leaf (7))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (3)) (.leaf (2)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (3)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (5)) (.leaf (2)))) (.branch 41 (.leaf (1)) (.branch 42 (.leaf (4)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (3)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (8))) (.branch 49 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_6150
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 12 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 13 (.leaf (-17)) (.branch 38 (.leaf (-19)) (.leaf (-20))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 27 (.leaf (-8)) (.branch 44 (.leaf (-10)) (.leaf (-11))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-14)) (.branch 21 (.leaf (-15)) (.leaf (-16))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (-2))) (.branch 37 (.leaf (-3)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 6 (.leaf (0)) (.branch 39 (.leaf (-32)) (.leaf (-33)))),
  (.branch 14 (.leaf (0)) (.leaf (-36))),
  (.branch 31 (.leaf (0)) (.leaf (-19))),
  (.branch 48 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 48 (.branch 39 (.leaf (-20)) (.leaf (-17))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 45 (.leaf (-11)) (.leaf (-9))),
  (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-12))) (.branch 49 (.leaf (-8)) (.leaf (-4)))),
  (.branch 47 (.branch 38 (.leaf (-5)) (.branch 46 (.leaf (-4)) (.leaf (-3)))) (.branch 48 (.leaf (-2)) (.branch 49 (.leaf (-1)) (.leaf (0))))),
  (.branch 45 (.branch 43 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-14)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 44 (.branch 41 (.branch 40 (.leaf (-33)) (.leaf (-30))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-24)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 32 (.branch 23 (.branch 18 (.branch 16 (.branch 15 (.leaf (-36)) (.leaf (-35))) (.branch 17 (.leaf (-34)) (.leaf (-33)))) (.branch 20 (.branch 19 (.leaf (-32)) (.leaf (-31))) (.branch 21 (.leaf (-30)) (.branch 22 (.leaf (-29)) (.leaf (-28)))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-27)) (.leaf (-26))) (.branch 26 (.leaf (-25)) (.leaf (-24)))) (.branch 29 (.branch 28 (.leaf (-23)) (.leaf (-22))) (.branch 30 (.leaf (-21)) (.branch 31 (.leaf (-20)) (.leaf (-19))))))) (.branch 41 (.branch 36 (.branch 34 (.branch 33 (.leaf (-18)) (.leaf (-17))) (.branch 35 (.leaf (-16)) (.leaf (-15)))) (.branch 38 (.branch 37 (.leaf (-14)) (.leaf (-13))) (.branch 39 (.leaf (-12)) (.branch 40 (.leaf (-11)) (.leaf (-10)))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 44 (.leaf (-7)) (.leaf (-6)))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 35 (.branch 33 (.branch 32 (.leaf (-19)) (.leaf (-18))) (.branch 34 (.leaf (-17)) (.leaf (-16)))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-14))) (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-12)) (.leaf (-11)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-8)) (.branch 44 (.leaf (-7)) (.leaf (-6))))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_313_6151 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (6)))) (.branch 16 (.leaf (8)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (1)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (7)) (.leaf (3))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (0)) (.leaf (6))))) (.branch 34 (.branch 32 (.leaf (8)) (.branch 33 (.leaf (1)) (.leaf (3)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (2)) (.leaf (4)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (5)))) (.branch 41 (.leaf (7)) (.branch 42 (.leaf (3)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (1)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (6))) (.branch 49 (.leaf (8)) (.leaf (3))))))))
  code := certificateP9_6151
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 13 (.leaf (-17)) (.branch 38 (.leaf (-19)) (.leaf (-20))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 14 (.leaf (-18)) (.branch 20 (.leaf (-19)) (.leaf (-20))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-16))) (.branch 19 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-13)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.leaf (-32))),
  (.branch 15 (.leaf (0)) (.branch 31 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-29))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (-2)) (.leaf (-4))))]
  high := ![(.branch 48 (.branch 39 (.leaf (-20)) (.leaf (-17))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 47 (.branch 46 (.leaf (-20)) (.leaf (-16))) (.branch 48 (.leaf (-12)) (.branch 49 (.leaf (-8)) (.leaf (-4))))),
  (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 47 (.branch 38 (.leaf (-14)) (.leaf (-12))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 44 (.branch 41 (.branch 7 (.leaf (-32)) (.branch 24 (.leaf (-31)) (.leaf (-30)))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-24)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 32 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-3)))),
  (.branch 44 (.branch 25 (.branch 8 (.leaf (-29)) (.leaf (-28))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-24)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 33 (.leaf (-4)) (.leaf (-3)))]
def witnessP9_313_6152 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (2)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (5)) (.leaf (7))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (5))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (0)) (.leaf (6))))) (.branch 34 (.branch 32 (.leaf (3)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 35 (.leaf (5)) (.branch 36 (.leaf (2)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (4)) (.branch 39 (.leaf (1)) (.leaf (0)))) (.branch 41 (.leaf (3)) (.branch 42 (.leaf (5)) (.leaf (8))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (4)) (.leaf (0))) (.branch 49 (.leaf (3)) (.leaf (5))))))))
  code := certificateP9_6152
  counts := ![(.branch 23 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 48 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 40 (.leaf (-15)) (.leaf (-16)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 14 (.leaf (-18)) (.leaf (-19)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-9)) (.leaf (-10)))),
  (.branch 25 (.branch 17 (.leaf (0)) (.leaf (-1))) (.branch 42 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-19))),
  (.branch 18 (.leaf (0)) (.leaf (-32))),
  (.branch 43 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 45 (.branch 41 (.leaf (-16)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 47 (.branch 40 (.leaf (-19)) (.leaf (-16))) (.branch 48 (.leaf (-12)) (.branch 49 (.leaf (-8)) (.leaf (-4))))),
  (.branch 47 (.branch 37 (.leaf (-17)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 33 (.leaf (-4)) (.leaf (-3))),
  (.branch 39 (.branch 30 (.leaf (-10)) (.leaf (-9))) (.branch 48 (.leaf (-8)) (.branch 49 (.leaf (-6)) (.leaf (-4))))),
  (.branch 44 (.branch 43 (.leaf (-3)) (.leaf (-2))) (.branch 45 (.leaf (-1)) (.leaf (0)))),
  (.branch 40 (.branch 35 (.branch 33 (.branch 32 (.leaf (-19)) (.leaf (-18))) (.branch 34 (.leaf (-17)) (.leaf (-16)))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-14))) (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-12)) (.leaf (-11)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-8)) (.branch 44 (.leaf (-7)) (.leaf (-6))))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (-32)) (.leaf (-31))) (.branch 21 (.leaf (-30)) (.leaf (-29)))) (.branch 24 (.branch 23 (.leaf (-28)) (.leaf (-27))) (.branch 25 (.leaf (-26)) (.leaf (-25))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-24)) (.leaf (-23))) (.branch 29 (.leaf (-22)) (.leaf (-21)))) (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-19))) (.branch 33 (.leaf (-18)) (.leaf (-17)))))) (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-12)) (.leaf (-11))) (.branch 41 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_313_6153 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (7)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (5)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (3)) (.leaf (4))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (3)) (.branch 33 (.leaf (0)) (.leaf (8)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (2)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (4)) (.branch 39 (.leaf (1)) (.leaf (0)))) (.branch 41 (.leaf (3)) (.branch 42 (.leaf (5)) (.leaf (1))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (6)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (3)) (.leaf (4))))))))
  code := certificateP9_6153
  counts := ![(.branch 22 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.branch 36 (.leaf (-17)) (.leaf (-18))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))) (.branch 14 (.leaf (-15)) (.branch 18 (.leaf (-16)) (.leaf (-17))))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 21 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-41))),
  (.branch 34 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 48 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 44 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 47 (.branch 29 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 33 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 45 (.branch 43 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-14)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-41)) (.leaf (-40))) (.branch 12 (.leaf (-39)) (.branch 13 (.leaf (-38)) (.leaf (-37))))) (.branch 16 (.branch 15 (.leaf (-36)) (.leaf (-35))) (.branch 17 (.leaf (-34)) (.branch 18 (.leaf (-33)) (.leaf (-32)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-31)) (.leaf (-30))) (.branch 22 (.leaf (-29)) (.branch 23 (.leaf (-28)) (.leaf (-27))))) (.branch 26 (.branch 25 (.leaf (-26)) (.leaf (-25))) (.branch 27 (.leaf (-24)) (.branch 28 (.leaf (-23)) (.leaf (-22))))))) (.branch 39 (.branch 34 (.branch 31 (.branch 30 (.leaf (-21)) (.leaf (-20))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-18)) (.leaf (-17))))) (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-12)) (.leaf (-11))) (.branch 41 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_313_6154 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (7)) (.branch 11 (.leaf (2)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (8)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (7))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (6)) (.branch 30 (.leaf (0)) (.leaf (4))))) (.branch 34 (.branch 32 (.leaf (3)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 35 (.leaf (8)) (.branch 36 (.leaf (2)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (5)) (.branch 39 (.leaf (1)) (.leaf (0)))) (.branch 41 (.leaf (3)) (.branch 42 (.leaf (7)) (.leaf (4))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (6)) (.leaf (0))) (.branch 49 (.leaf (3)) (.leaf (8))))))))
  code := certificateP9_6154
  counts := ![(.branch 23 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 48 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 40 (.leaf (-15)) (.leaf (-16)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 14 (.leaf (-18)) (.leaf (-19)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 13 (.leaf (0)) (.branch 29 (.leaf (-4)) (.leaf (-5)))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (-7)) (.leaf (-9)))),
  (.leaf (0))]
  high := ![(.branch 45 (.branch 41 (.leaf (-16)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 47 (.branch 40 (.leaf (-19)) (.leaf (-16))) (.branch 48 (.leaf (-12)) (.branch 49 (.leaf (-8)) (.leaf (-4))))),
  (.branch 47 (.branch 37 (.leaf (-17)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 33 (.leaf (-4)) (.leaf (-3))),
  (.branch 46 (.branch 44 (.leaf (-14)) (.branch 45 (.leaf (-12)) (.leaf (-10)))) (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-6))) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-13)) (.branch 40 (.leaf (-12)) (.leaf (-11)))) (.branch 42 (.leaf (-10)) (.branch 43 (.leaf (-9)) (.leaf (-8))))) (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 48 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.leaf (-2)))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (0))]
def witnessP9_313_6155 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (2)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (7)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (4)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.leaf (5))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (6)) (.branch 30 (.leaf (0)) (.leaf (3))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (4)) (.leaf (2)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (5)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (2)))) (.branch 41 (.leaf (1)) (.branch 42 (.leaf (8)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (4)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (3))) (.branch 49 (.leaf (1)) (.leaf (5))))))))
  code := certificateP9_6155
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 13 (.leaf (-17)) (.branch 38 (.leaf (-19)) (.leaf (-20))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 27 (.leaf (-8)) (.branch 44 (.leaf (-10)) (.leaf (-11))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-14)) (.branch 21 (.leaf (-15)) (.leaf (-16))))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (-9)) (.leaf (-10)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-21))),
  (.branch 17 (.leaf (0)) (.leaf (-33))),
  (.branch 42 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 48 (.branch 39 (.leaf (-20)) (.leaf (-17))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 45 (.leaf (-11)) (.leaf (-9))),
  (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-12))) (.branch 49 (.leaf (-8)) (.leaf (-4)))),
  (.branch 40 (.leaf (-8)) (.branch 49 (.leaf (-6)) (.leaf (-3)))),
  (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 38 (.leaf (-1)) (.leaf (0))),
  (.branch 39 (.branch 34 (.branch 31 (.branch 30 (.leaf (-21)) (.leaf (-20))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-18)) (.leaf (-17))))) (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (-33)) (.leaf (-32))) (.branch 20 (.leaf (-31)) (.leaf (-30)))) (.branch 23 (.branch 22 (.leaf (-29)) (.leaf (-28))) (.branch 24 (.leaf (-27)) (.leaf (-26))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-25)) (.leaf (-24))) (.branch 28 (.leaf (-23)) (.leaf (-22)))) (.branch 31 (.branch 30 (.leaf (-21)) (.leaf (-20))) (.branch 32 (.leaf (-19)) (.leaf (-18)))))) (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (-17)) (.leaf (-16))) (.branch 36 (.leaf (-15)) (.leaf (-14)))) (.branch 39 (.branch 38 (.leaf (-13)) (.leaf (-12))) (.branch 40 (.leaf (-11)) (.leaf (-10))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 44 (.leaf (-7)) (.leaf (-6)))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_313_6156 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (5)) (.leaf (8)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (6)) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (2)) (.leaf (7))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (0)) (.leaf (2))))) (.branch 34 (.branch 32 (.leaf (4)) (.branch 33 (.leaf (1)) (.leaf (3)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (6)) (.leaf (8)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (2)) (.branch 39 (.leaf (0)) (.leaf (1)))) (.branch 41 (.leaf (4)) (.branch 42 (.leaf (3)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (5)) (.branch 45 (.leaf (2)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (4))) (.branch 49 (.leaf (3)) (.leaf (7))))))))
  code := certificateP9_6156
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-19)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-17)) (.leaf (-18)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-25)) (.leaf (-32)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-7))) (.branch 20 (.leaf (-8)) (.branch 34 (.leaf (-9)) (.leaf (-11))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (-3))) (.branch 48 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.leaf (0)) (.branch 44 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-13)) (.leaf (-15)))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 48 (.branch 31 (.leaf (-20)) (.leaf (-18))) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 47 (.branch 34 (.leaf (-18)) (.leaf (-16))) (.branch 48 (.leaf (-12)) (.branch 49 (.leaf (-8)) (.leaf (-4))))),
  (.branch 47 (.branch 10 (.leaf (-32)) (.branch 46 (.leaf (-31)) (.leaf (-25)))) (.branch 48 (.leaf (-19)) (.branch 49 (.leaf (-13)) (.leaf (-7))))),
  (.branch 35 (.leaf (-11)) (.leaf (-7))),
  (.branch 49 (.leaf (-6)) (.leaf (-4))),
  (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2))))),
  (.branch 43 (.branch 39 (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))) (.branch 41 (.branch 40 (.leaf (-12)) (.leaf (-11))) (.branch 42 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.leaf (-2)))))),
  (.leaf (0)),
  (.branch 43 (.branch 40 (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-12)) (.leaf (-11)))) (.branch 41 (.leaf (-10)) (.branch 42 (.leaf (-9)) (.leaf (-8))))) (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_313_6157 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (5)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (8)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (6)) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (7))) (.branch 24 (.leaf (2)) (.leaf (4))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (0)) (.leaf (2))))) (.branch 34 (.branch 32 (.leaf (8)) (.branch 33 (.leaf (1)) (.leaf (3)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (6)) (.leaf (4)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (2)) (.branch 39 (.leaf (0)) (.leaf (1)))) (.branch 41 (.leaf (7)) (.branch 42 (.leaf (3)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (5)) (.branch 45 (.leaf (2)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (8))) (.branch 49 (.leaf (3)) (.leaf (4))))))))
  code := certificateP9_6157
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-19)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-17)) (.leaf (-18)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-25)) (.leaf (-32)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-7))) (.branch 20 (.leaf (-8)) (.branch 34 (.leaf (-9)) (.leaf (-11))))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.branch 44 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-13)) (.leaf (-15)))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (-10)) (.leaf (-11)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (-1))) (.branch 48 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 48 (.branch 31 (.leaf (-20)) (.leaf (-18))) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 47 (.branch 34 (.leaf (-18)) (.leaf (-16))) (.branch 48 (.leaf (-12)) (.branch 49 (.leaf (-8)) (.leaf (-4))))),
  (.branch 47 (.branch 10 (.leaf (-32)) (.branch 46 (.leaf (-31)) (.leaf (-25)))) (.branch 48 (.leaf (-19)) (.branch 49 (.leaf (-13)) (.leaf (-7))))),
  (.branch 35 (.leaf (-11)) (.leaf (-7))),
  (.branch 38 (.leaf (-1)) (.leaf (0))),
  (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2))))),
  (.branch 43 (.branch 39 (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))) (.branch 41 (.branch 40 (.leaf (-12)) (.leaf (-11))) (.branch 42 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 45 (.branch 42 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 46 (.leaf (-6)) (.leaf (-5))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 49 (.leaf (-3)) (.leaf (-2)))]
def witnessP9_313_6158 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (2)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (8)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (1)) (.leaf (4))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (7)) (.branch 30 (.leaf (0)) (.leaf (6))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (3)) (.leaf (2)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (4)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (5)) (.leaf (2)))) (.branch 41 (.leaf (1)) (.branch 42 (.leaf (8)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (3)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (6))) (.branch 49 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_6158
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 13 (.leaf (-17)) (.branch 38 (.leaf (-19)) (.leaf (-20))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 27 (.leaf (-8)) (.branch 44 (.leaf (-10)) (.leaf (-11))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-14)) (.branch 21 (.leaf (-15)) (.leaf (-16))))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (-9)) (.leaf (-10)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 39 (.leaf (-32)) (.leaf (-33)))),
  (.branch 14 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.leaf (-21))),
  (.branch 17 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 48 (.branch 39 (.leaf (-20)) (.leaf (-17))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 45 (.leaf (-11)) (.leaf (-9))),
  (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-12))) (.branch 49 (.leaf (-8)) (.leaf (-4)))),
  (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 38 (.leaf (-1)) (.leaf (0))),
  (.branch 44 (.branch 41 (.branch 40 (.leaf (-33)) (.leaf (-30))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-24)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 32 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-3)))),
  (.branch 39 (.branch 34 (.branch 31 (.branch 30 (.leaf (-21)) (.leaf (-20))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-18)) (.leaf (-17))))) (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_313_6159 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (8)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (2)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (6)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (8)) (.leaf (7))) (.branch 24 (.leaf (0)) (.leaf (1))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (4)) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (1)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (6)) (.branch 33 (.leaf (5)) (.leaf (2)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (4)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (3)) (.branch 39 (.leaf (0)) (.leaf (8)))) (.branch 41 (.leaf (7)) (.branch 42 (.leaf (1)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (5)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (6))) (.branch 49 (.leaf (3)) (.leaf (4))))))))
  code := certificateP9_6159
  counts := ![(.branch 24 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 35 (.branch 28 (.leaf (7)) (.branch 31 (.leaf (8)) (.leaf (9)))) (.branch 43 (.branch 39 (.leaf (10)) (.leaf (11))) (.branch 47 (.leaf (12)) (.leaf (13)))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 46 (.leaf (8)) (.leaf (9)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-20))) (.branch 31 (.leaf (-24)) (.leaf (-26)))),
  (.branch 30 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 46 (.leaf (-12)) (.leaf (-15)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 17 (.leaf (-7)) (.branch 34 (.leaf (-10)) (.leaf (-11))))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (-1))) (.branch 38 (.leaf (-6)) (.leaf (-8)))),
  (.branch 37 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.branch 45 (.leaf (-6)) (.leaf (-7)))),
  (.branch 15 (.leaf (0)) (.branch 48 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.leaf (-27)))]
  high := ![(.branch 40 (.branch 32 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 48 (.branch 44 (.leaf (-23)) (.leaf (-22))) (.branch 49 (.leaf (-15)) (.leaf (-8))))),
  (.branch 48 (.branch 47 (.leaf (-15)) (.leaf (-12))) (.branch 49 (.leaf (-9)) (.leaf (-6)))),
  (.branch 46 (.branch 35 (.leaf (-11)) (.branch 45 (.leaf (-10)) (.leaf (-9)))) (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5))))),
  (.branch 39 (.leaf (-8)) (.leaf (-7))),
  (.branch 38 (.leaf (-3)) (.leaf (0))),
  (.branch 47 (.branch 46 (.leaf (-7)) (.leaf (-6))) (.branch 48 (.leaf (-5)) (.branch 49 (.leaf (-4)) (.leaf (-3))))),
  (.branch 49 (.leaf (-6)) (.leaf (-3))),
  (.branch 45 (.branch 42 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 46 (.leaf (-6)) (.leaf (-5))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 44 (.branch 41 (.branch 5 (.leaf (-27)) (.branch 23 (.leaf (-26)) (.leaf (-25)))) (.branch 42 (.leaf (-23)) (.branch 43 (.leaf (-21)) (.leaf (-19))))) (.branch 47 (.branch 45 (.leaf (-17)) (.branch 46 (.leaf (-15)) (.leaf (-13)))) (.branch 48 (.leaf (-11)) (.branch 49 (.leaf (-9)) (.leaf (-7))))))]
def witnessP9_313_6160 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (6)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (0))) (.branch 24 (.leaf (2)) (.leaf (1))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (7))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (4)) (.leaf (1)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (2)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (1)) (.branch 39 (.leaf (5)) (.leaf (0)))) (.branch 41 (.leaf (3)) (.branch 42 (.leaf (1)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (4)) (.branch 45 (.leaf (0)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (8)) (.leaf (0))) (.branch 49 (.leaf (2)) (.leaf (1))))))))
  code := certificateP9_6160
  counts := ![(.branch 23 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))) (.branch 37 (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 43 (.branch 40 (.leaf (14)) (.leaf (15))) (.branch 45 (.leaf (16)) (.branch 48 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 46 (.branch 42 (.leaf (11)) (.leaf (12))) (.branch 50 (.leaf (13)) (.leaf (14)))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 20 (.leaf (-10)) (.branch 45 (.leaf (-12)) (.leaf (-13))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 27 (.leaf (-13)) (.branch 30 (.leaf (-17)) (.leaf (-21))))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (-5))) (.branch 44 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (-32)) (.leaf (-34)))),
  (.branch 14 (.leaf (0)) (.leaf (-36))),
  (.branch 31 (.leaf (0)) (.leaf (-19))),
  (.branch 47 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 46 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 43 (.branch 35 (.branch 31 (.leaf (-21)) (.leaf (-20))) (.branch 39 (.leaf (-19)) (.leaf (-18)))) (.branch 48 (.branch 47 (.leaf (-17)) (.leaf (-12))) (.branch 49 (.leaf (-7)) (.leaf (-2))))),
  (.branch 37 (.leaf (-3)) (.leaf (-2))),
  (.branch 45 (.branch 42 (.branch 29 (.leaf (-19)) (.leaf (-18))) (.branch 43 (.leaf (-16)) (.branch 44 (.leaf (-14)) (.leaf (-12))))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 47 (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.leaf (-5)) (.branch 49 (.leaf (-4)) (.leaf (-3))))),
  (.branch 44 (.branch 41 (.branch 23 (.leaf (-34)) (.branch 40 (.leaf (-33)) (.leaf (-30)))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-24)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 32 (.branch 23 (.branch 18 (.branch 16 (.branch 15 (.leaf (-36)) (.leaf (-35))) (.branch 17 (.leaf (-34)) (.leaf (-33)))) (.branch 20 (.branch 19 (.leaf (-32)) (.leaf (-31))) (.branch 21 (.leaf (-30)) (.branch 22 (.leaf (-29)) (.leaf (-28)))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-27)) (.leaf (-26))) (.branch 26 (.leaf (-25)) (.leaf (-24)))) (.branch 29 (.branch 28 (.leaf (-23)) (.leaf (-22))) (.branch 30 (.leaf (-21)) (.branch 31 (.leaf (-20)) (.leaf (-19))))))) (.branch 41 (.branch 36 (.branch 34 (.branch 33 (.leaf (-18)) (.leaf (-17))) (.branch 35 (.leaf (-16)) (.leaf (-15)))) (.branch 38 (.branch 37 (.leaf (-14)) (.leaf (-13))) (.branch 39 (.leaf (-12)) (.branch 40 (.leaf (-11)) (.leaf (-10)))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 44 (.leaf (-7)) (.leaf (-6)))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 35 (.branch 33 (.branch 32 (.leaf (-19)) (.leaf (-18))) (.branch 34 (.leaf (-17)) (.leaf (-16)))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-14))) (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-12)) (.leaf (-11)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-8)) (.branch 44 (.leaf (-7)) (.leaf (-6))))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_313_6161 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (7)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (1)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (8)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (6))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (4)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (2)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (7)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (3)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (5)) (.leaf (1)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (4)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (8)) (.leaf (1))) (.branch 49 (.leaf (0)) (.leaf (6))))))))
  code := certificateP9_6161
  counts := ![(.branch 24 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 38 (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 43 (.branch 41 (.leaf (14)) (.leaf (15))) (.branch 46 (.leaf (16)) (.branch 49 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 8 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 31 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 48 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 26 (.leaf (-9)) (.leaf (-10)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-17)))) (.branch 33 (.leaf (-21)) (.branch 36 (.leaf (-25)) (.leaf (-29))))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-15)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-41))),
  (.branch 12 (.leaf (0)) (.branch 28 (.leaf (-14)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-16))),
  (.branch 22 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 44 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.leaf (-7)))),
  (.branch 41 (.branch 37 (.leaf (-29)) (.leaf (-28))) (.branch 45 (.leaf (-27)) (.branch 49 (.leaf (-26)) (.leaf (-21))))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-16)) (.leaf (-14))) (.branch 45 (.leaf (-12)) (.leaf (-10)))) (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-6))) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 42 (.branch 38 (.branch 4 (.leaf (-41)) (.branch 21 (.leaf (-40)) (.leaf (-39)))) (.branch 40 (.branch 39 (.leaf (-36)) (.leaf (-33))) (.branch 41 (.leaf (-30)) (.leaf (-27))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-24)) (.leaf (-21))) (.branch 45 (.leaf (-18)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 47 (.branch 29 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-12)) (.leaf (-11))) (.branch 41 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_313_6162 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (0)) (.leaf (3)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (6))) (.branch 24 (.leaf (0)) (.leaf (8))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (4)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (5)) (.leaf (0)))) (.branch 35 (.leaf (6)) (.branch 36 (.leaf (0)) (.leaf (2)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (7)) (.branch 39 (.leaf (0)) (.leaf (3)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (4))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (5)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (6))) (.branch 49 (.leaf (0)) (.leaf (8))))))))
  code := certificateP9_6162
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 36 (.branch 29 (.branch 26 (.leaf (10)) (.leaf (11))) (.branch 31 (.leaf (12)) (.branch 34 (.leaf (13)) (.leaf (14))))) (.branch 44 (.branch 39 (.leaf (15)) (.branch 41 (.leaf (16)) (.leaf (17)))) (.branch 46 (.leaf (18)) (.branch 49 (.leaf (19)) (.leaf (20))))))),
  (.branch 22 (.branch 2 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-19)) (.leaf (-20)))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (-9)) (.leaf (-10)))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 13 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.branch 47 (.leaf (-3)) (.leaf (-2))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))),
  (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-18))) (.branch 43 (.leaf (-16)) (.branch 44 (.leaf (-14)) (.leaf (-12))))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 46 (.branch 44 (.branch 31 (.leaf (-15)) (.leaf (-14))) (.branch 45 (.leaf (-12)) (.leaf (-10)))) (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-6))) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 36 (.leaf (-5)) (.branch 49 (.leaf (-4)) (.leaf (-2)))),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-12)) (.branch 40 (.leaf (-11)) (.leaf (-10)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_313_6163 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (3)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (7))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (4)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (5)) (.leaf (0)))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (6)) (.branch 39 (.leaf (1)) (.leaf (0)))) (.branch 41 (.leaf (2)) (.branch 42 (.leaf (4)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (3)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (5)) (.leaf (2))) (.branch 49 (.leaf (0)) (.leaf (8))))))))
  code := certificateP9_6163
  counts := ![(.branch 24 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 37 (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 34 (.leaf (12)) (.leaf (13))))) (.branch 43 (.branch 40 (.leaf (14)) (.leaf (15))) (.branch 46 (.leaf (16)) (.branch 49 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 34 (.leaf (-11)) (.leaf (-12)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 23 (.leaf (-13)) (.branch 44 (.leaf (-14)) (.leaf (-17))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (-3))) (.branch 41 (.leaf (-7)) (.branch 48 (.leaf (-8)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-15)) (.leaf (-16)))),
  (.branch 8 (.leaf (0)) (.branch 33 (.leaf (-5)) (.leaf (-6)))),
  (.branch 13 (.leaf (0)) (.leaf (-12))),
  (.branch 25 (.leaf (0)) (.leaf (-25))),
  (.leaf (0))]
  high := ![(.branch 41 (.branch 35 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 44 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7))))),
  (.branch 47 (.branch 45 (.leaf (-17)) (.branch 46 (.leaf (-15)) (.leaf (-13)))) (.branch 48 (.leaf (-11)) (.branch 49 (.leaf (-9)) (.leaf (-7))))),
  (.branch 49 (.leaf (-9)) (.leaf (-7))),
  (.branch 47 (.branch 37 (.leaf (-17)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-16)) (.leaf (-14))) (.branch 45 (.leaf (-12)) (.leaf (-10)))) (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-6))) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 48 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 49 (.leaf (-4)) (.leaf (-3)))),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-12)) (.branch 40 (.leaf (-11)) (.leaf (-10)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (-25)) (.branch 27 (.leaf (-24)) (.leaf (-23)))) (.branch 29 (.leaf (-22)) (.branch 30 (.leaf (-21)) (.leaf (-20))))) (.branch 34 (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-18)) (.leaf (-17)))) (.branch 35 (.leaf (-16)) (.branch 36 (.leaf (-15)) (.leaf (-14)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-12)) (.leaf (-11)))) (.branch 41 (.leaf (-10)) (.branch 42 (.leaf (-9)) (.leaf (-8))))) (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_313_6164 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (8)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (3)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (7)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (1)) (.leaf (5))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (4)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (8)) (.leaf (0)))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (6)) (.branch 39 (.leaf (1)) (.leaf (0)))) (.branch 41 (.leaf (4)) (.branch 42 (.leaf (0)) (.leaf (2))))) (.branch 46 (.branch 44 (.leaf (3)) (.branch 45 (.leaf (0)) (.leaf (7)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6164
  counts := ![(.branch 23 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))) (.branch 37 (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 34 (.leaf (12)) (.leaf (13))))) (.branch 42 (.branch 40 (.leaf (14)) (.leaf (15))) (.branch 45 (.leaf (16)) (.branch 48 (.leaf (17)) (.leaf (18))))))),
  (.branch 24 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 17 (.leaf (-11)) (.branch 42 (.leaf (-13)) (.leaf (-14))))),
  (.branch 24 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 31 (.leaf (-12)) (.leaf (-13)))),
  (.branch 27 (.branch 6 (.leaf (0)) (.leaf (-3))) (.branch 49 (.leaf (-6)) (.leaf (-7)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-16))) (.branch 19 (.leaf (-17)) (.leaf (-18)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-8))) (.branch 41 (.leaf (-10)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-12))),
  (.branch 21 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 46 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 40 (.branch 32 (.leaf (-13)) (.leaf (-12))) (.branch 48 (.leaf (-11)) (.branch 49 (.leaf (-9)) (.leaf (-7))))),
  (.leaf (-7)),
  (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 45 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-8)))) (.branch 47 (.branch 46 (.leaf (-7)) (.leaf (-6))) (.branch 48 (.leaf (-5)) (.branch 49 (.leaf (-4)) (.leaf (-3)))))),
  (.leaf (0)),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-12)) (.branch 40 (.leaf (-11)) (.leaf (-10)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))),
  (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (-17)) (.leaf (-16))) (.branch 36 (.leaf (-15)) (.leaf (-14)))) (.branch 39 (.branch 38 (.leaf (-13)) (.leaf (-12))) (.branch 40 (.leaf (-11)) (.leaf (-10))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 44 (.leaf (-7)) (.leaf (-6)))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_313_6165 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (3)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1)))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (0)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (3))) (.branch 24 (.leaf (2)) (.leaf (0))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (5)) (.branch 27 (.leaf (1)) (.leaf (4)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (2)) (.leaf (3))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (2)))) (.branch 35 (.leaf (7)) (.branch 36 (.leaf (0)) (.leaf (1)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (3)) (.branch 39 (.leaf (2)) (.leaf (0)))) (.branch 41 (.leaf (5)) (.branch 42 (.leaf (1)) (.leaf (2))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (4)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_6165
  counts := ![(.branch 25 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 29 (.leaf (7)) (.branch 33 (.leaf (8)) (.leaf (9)))) (.branch 44 (.branch 40 (.leaf (10)) (.leaf (11))) (.branch 48 (.leaf (12)) (.leaf (13)))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 42 (.leaf (9)) (.branch 47 (.leaf (10)) (.leaf (11)))))),
  (.branch 24 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 30 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-23))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-17)) (.leaf (-22)))) (.branch 19 (.leaf (-27)) (.branch 22 (.leaf (-31)) (.leaf (-42))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-6)))) (.branch 39 (.branch 34 (.leaf (-7)) (.leaf (-9))) (.branch 43 (.leaf (-10)) (.leaf (-13))))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-22)) (.leaf (-33)))),
  (.branch 12 (.leaf (0)) (.branch 28 (.leaf (-14)) (.leaf (-16)))),
  (.branch 7 (.leaf (0)) (.branch 41 (.leaf (-11)) (.leaf (-13)))),
  (.branch 16 (.leaf (0)) (.leaf (-34))),
  (.branch 35 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 41 (.branch 2 (.leaf (-23)) (.branch 37 (.leaf (-22)) (.leaf (-21)))) (.branch 45 (.leaf (-20)) (.branch 49 (.leaf (-19)) (.leaf (-11))))),
  (.branch 38 (.branch 28 (.branch 23 (.leaf (-42)) (.leaf (-41))) (.branch 33 (.leaf (-40)) (.leaf (-39)))) (.branch 48 (.branch 43 (.leaf (-38)) (.leaf (-37))) (.branch 49 (.leaf (-31)) (.leaf (-25))))),
  (.branch 44 (.leaf (-13)) (.leaf (-12))),
  (.branch 47 (.branch 24 (.leaf (-33)) (.branch 39 (.leaf (-32)) (.leaf (-29)))) (.branch 48 (.leaf (-24)) (.branch 49 (.leaf (-19)) (.leaf (-14))))),
  (.branch 47 (.branch 29 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 45 (.branch 43 (.branch 42 (.leaf (-13)) (.leaf (-12))) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 47 (.branch 46 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))))),
  (.branch 33 (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (-34)) (.leaf (-33))) (.branch 19 (.leaf (-32)) (.leaf (-31)))) (.branch 22 (.branch 21 (.leaf (-30)) (.leaf (-29))) (.branch 23 (.leaf (-28)) (.leaf (-27))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-26)) (.leaf (-25))) (.branch 27 (.leaf (-24)) (.leaf (-23)))) (.branch 30 (.branch 29 (.leaf (-22)) (.leaf (-21))) (.branch 31 (.leaf (-20)) (.branch 32 (.leaf (-19)) (.leaf (-18))))))) (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (-17)) (.leaf (-16))) (.branch 36 (.leaf (-15)) (.leaf (-14)))) (.branch 39 (.branch 38 (.leaf (-13)) (.leaf (-12))) (.branch 40 (.leaf (-11)) (.leaf (-10))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 44 (.leaf (-7)) (.leaf (-6)))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 38 (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-14)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-12)) (.leaf (-11))) (.branch 41 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_313_6166 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (1)) (.leaf (7))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (2)) (.leaf (4))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (0)) (.leaf (6))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (5)) (.leaf (0)))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (1)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (0)))) (.branch 41 (.leaf (4)) (.branch 42 (.leaf (1)) (.leaf (8))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (3)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_6166
  counts := ![(.branch 23 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 48 (.leaf (13)) (.leaf (14)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 42 (.leaf (8)) (.branch 47 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 40 (.leaf (-10)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-2)) (.leaf (-4)))) (.branch 39 (.branch 29 (.leaf (-6)) (.leaf (-7))) (.branch 49 (.leaf (-9)) (.leaf (-11))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 8 (.leaf (0)) (.branch 41 (.leaf (-26)) (.leaf (-27)))),
  (.branch 16 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-19))),
  (.branch 18 (.leaf (0)) (.leaf (-32))),
  (.branch 43 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 45 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 49 (.leaf (-10)) (.leaf (-7)))),
  (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-11)),
  (.branch 47 (.branch 37 (.leaf (-17)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 45 (.branch 43 (.branch 42 (.leaf (-27)) (.leaf (-24))) (.branch 44 (.leaf (-21)) (.leaf (-18)))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-12))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 17 (.leaf (-2)) (.branch 34 (.leaf (-1)) (.leaf (0)))),
  (.branch 40 (.branch 35 (.branch 33 (.branch 32 (.leaf (-19)) (.leaf (-18))) (.branch 34 (.leaf (-17)) (.leaf (-16)))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-14))) (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-12)) (.leaf (-11)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-8)) (.branch 44 (.leaf (-7)) (.leaf (-6))))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (-32)) (.leaf (-31))) (.branch 21 (.leaf (-30)) (.leaf (-29)))) (.branch 24 (.branch 23 (.leaf (-28)) (.leaf (-27))) (.branch 25 (.leaf (-26)) (.leaf (-25))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-24)) (.leaf (-23))) (.branch 29 (.leaf (-22)) (.leaf (-21)))) (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-19))) (.branch 33 (.leaf (-18)) (.leaf (-17)))))) (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-12)) (.leaf (-11))) (.branch 41 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_313_6167 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (6)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (3)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (8)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (6))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (7))) (.branch 24 (.leaf (1)) (.leaf (4))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (8)) (.branch 33 (.leaf (0)) (.leaf (4)))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (5)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (7)))) (.branch 41 (.leaf (4)) (.branch 42 (.leaf (2)) (.leaf (6))))) (.branch 46 (.branch 44 (.leaf (3)) (.branch 45 (.leaf (0)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (5)) (.leaf (8))) (.branch 49 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_6167
  counts := ![(.branch 20 (.branch 8 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-21))),
  (.branch 2 (.leaf (0)) (.leaf (-31))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-7))) (.branch 27 (.leaf (-8)) (.leaf (-10)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-16))) (.branch 19 (.leaf (-17)) (.leaf (-18)))),
  (.branch 16 (.leaf (0)) (.branch 41 (.leaf (-2)) (.leaf (-3)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 29 (.leaf (-6)) (.branch 37 (.leaf (-7)) (.leaf (-8))))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (-29)) (.leaf (-31)))),
  (.branch 15 (.leaf (0)) (.branch 48 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 47 (.branch 27 (.leaf (-21)) (.branch 46 (.leaf (-20)) (.leaf (-16)))) (.branch 48 (.leaf (-12)) (.branch 49 (.leaf (-8)) (.leaf (-4))))),
  (.branch 47 (.branch 3 (.leaf (-31)) (.branch 39 (.leaf (-30)) (.leaf (-25)))) (.branch 48 (.leaf (-19)) (.branch 49 (.leaf (-13)) (.leaf (-7))))),
  (.branch 28 (.leaf (-10)) (.leaf (-7))),
  (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-1)) (.leaf (0)))),
  (.branch 48 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))),
  (.branch 46 (.branch 44 (.branch 31 (.leaf (-15)) (.leaf (-14))) (.branch 45 (.leaf (-12)) (.leaf (-10)))) (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-6))) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 44 (.branch 41 (.branch 24 (.leaf (-31)) (.leaf (-30))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-24)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.leaf (-6)) (.leaf (-3)))]
def witnessP9_313_6168 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (3)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (8)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (1))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (5)) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (1)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (2)) (.branch 33 (.leaf (7)) (.leaf (3)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (5)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (4)) (.branch 39 (.leaf (0)) (.leaf (6)))) (.branch 41 (.leaf (2)) (.branch 42 (.leaf (1)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (3)) (.branch 45 (.leaf (8)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (2))) (.branch 49 (.leaf (4)) (.leaf (5))))))))
  code := certificateP9_6168
  counts := ![(.branch 24 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 35 (.branch 28 (.leaf (7)) (.branch 31 (.leaf (8)) (.leaf (9)))) (.branch 43 (.branch 39 (.leaf (10)) (.leaf (11))) (.branch 47 (.leaf (12)) (.leaf (13)))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 46 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-20))) (.branch 31 (.leaf (-24)) (.leaf (-26)))),
  (.branch 30 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 46 (.leaf (-12)) (.leaf (-15)))),
  (.branch 6 (.leaf (0)) (.branch 48 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 17 (.leaf (-7)) (.branch 34 (.leaf (-10)) (.leaf (-11))))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (-1))) (.branch 38 (.leaf (-6)) (.leaf (-8)))),
  (.branch 37 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-27))),
  (.branch 7 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.branch 45 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 40 (.branch 32 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 48 (.branch 44 (.leaf (-23)) (.leaf (-22))) (.branch 49 (.leaf (-15)) (.leaf (-8))))),
  (.branch 48 (.branch 47 (.leaf (-15)) (.leaf (-12))) (.branch 49 (.leaf (-9)) (.leaf (-6)))),
  (.branch 49 (.leaf (-6)) (.leaf (-4))),
  (.branch 46 (.branch 35 (.leaf (-11)) (.branch 45 (.leaf (-10)) (.leaf (-9)))) (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5))))),
  (.branch 39 (.leaf (-8)) (.leaf (-7))),
  (.branch 38 (.leaf (-3)) (.leaf (0))),
  (.branch 44 (.branch 41 (.branch 5 (.leaf (-27)) (.branch 23 (.leaf (-26)) (.leaf (-25)))) (.branch 42 (.leaf (-23)) (.branch 43 (.leaf (-21)) (.leaf (-19))))) (.branch 47 (.branch 45 (.leaf (-17)) (.branch 46 (.leaf (-15)) (.leaf (-13)))) (.branch 48 (.leaf (-11)) (.branch 49 (.leaf (-9)) (.leaf (-7)))))),
  (.branch 41 (.branch 36 (.branch 34 (.branch 8 (.leaf (-18)) (.leaf (-17))) (.branch 35 (.leaf (-16)) (.leaf (-15)))) (.branch 38 (.branch 37 (.leaf (-14)) (.leaf (-13))) (.branch 39 (.leaf (-12)) (.branch 40 (.leaf (-11)) (.leaf (-10)))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 44 (.leaf (-7)) (.leaf (-6)))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_313_6169 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (3)) (.leaf (8)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (6)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (7)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (5))) (.branch 24 (.leaf (3)) (.leaf (1))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (4)) (.leaf (2)))) (.branch 29 (.leaf (8)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (6)) (.branch 33 (.leaf (3)) (.leaf (0)))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (1)) (.leaf (7)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (5)))) (.branch 41 (.leaf (1)) (.branch 42 (.leaf (2)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (4)) (.branch 45 (.leaf (8)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (3))) (.branch 49 (.leaf (6)) (.leaf (2))))))))
  code := certificateP9_6169
  counts := ![(.branch 21 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 41 (.leaf (7)) (.branch 46 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-16)) (.leaf (-17)))) (.branch 17 (.leaf (-18)) (.branch 21 (.leaf (-20)) (.leaf (-21))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-15))) (.branch 41 (.leaf (-18)) (.branch 46 (.leaf (-20)) (.leaf (-23))))),
  (.branch 28 (.branch 22 (.leaf (0)) (.leaf (-3))) (.branch 35 (.leaf (-8)) (.branch 42 (.leaf (-10)) (.leaf (-12))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 24 (.leaf (-6)) (.branch 39 (.leaf (-8)) (.leaf (-9))))),
  (.branch 10 (.leaf (0)) (.leaf (-20))),
  (.branch 6 (.leaf (0)) (.leaf (-32))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-38)) (.leaf (-40)))),
  (.branch 12 (.leaf (0)) (.branch 45 (.leaf (-14)) (.leaf (-15))))]
  high := ![(.branch 39 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-7))))),
  (.branch 48 (.branch 47 (.leaf (-23)) (.leaf (-19))) (.branch 49 (.leaf (-15)) (.leaf (-11)))),
  (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-9))) (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-3)) (.leaf (0))))),
  (.branch 40 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7)))),
  (.branch 46 (.branch 28 (.branch 11 (.leaf (-20)) (.leaf (-19))) (.branch 45 (.leaf (-18)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 44 (.branch 41 (.branch 7 (.leaf (-32)) (.branch 24 (.leaf (-31)) (.leaf (-30)))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-24)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 16 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 43 (.branch 39 (.branch 21 (.leaf (-40)) (.branch 38 (.leaf (-39)) (.leaf (-36)))) (.branch 41 (.branch 40 (.leaf (-33)) (.leaf (-30))) (.branch 42 (.leaf (-27)) (.leaf (-24))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-18)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-12))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_313_6170 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (8)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (3)) (.leaf (6)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (4)))) (.branch 16 (.leaf (7)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (5)) (.branch 20 (.leaf (2)) (.leaf (8)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.leaf (6))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (4)))) (.branch 29 (.leaf (7)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (5)) (.branch 33 (.leaf (8)) (.leaf (2)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (3)) (.leaf (6)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (4)))) (.branch 41 (.leaf (7)) (.branch 42 (.leaf (2)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (5)) (.branch 45 (.leaf (1)) (.leaf (8)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (3))) (.branch 49 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_6170
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-19)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-36)) (.leaf (-37)))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-8)) (.leaf (-9)))) (.branch 27 (.leaf (-10)) (.branch 34 (.leaf (-11)) (.leaf (-12))))),
  (.branch 11 (.leaf (0)) (.branch 23 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-19)) (.leaf (-20)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-11)) (.leaf (-12)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-18)))),
  (.branch 8 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 48 (.branch 31 (.leaf (-20)) (.leaf (-18))) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 47 (.branch 10 (.leaf (-37)) (.branch 46 (.leaf (-35)) (.leaf (-28)))) (.branch 48 (.leaf (-21)) (.branch 49 (.leaf (-14)) (.leaf (-7))))),
  (.branch 35 (.leaf (-12)) (.leaf (-7))),
  (.branch 49 (.leaf (-4)) (.leaf (-2))),
  (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-18))) (.branch 43 (.leaf (-16)) (.branch 44 (.leaf (-14)) (.leaf (-12))))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-10)) (.leaf (-8)))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 38 (.leaf (-1)) (.leaf (0))),
  (.branch 45 (.branch 43 (.branch 42 (.leaf (-18)) (.leaf (-16))) (.branch 44 (.leaf (-14)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 47 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))]
def witnessP9_313_6171 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (6)) (.leaf (7)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (3)) (.leaf (4)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (8)) (.leaf (6))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (5))) (.branch 24 (.leaf (4)) (.leaf (7))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (6)))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (4)) (.branch 33 (.leaf (5)) (.leaf (8)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (2)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (6)) (.branch 39 (.leaf (3)) (.leaf (4)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (7)) (.leaf (5))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (2)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (3)) (.leaf (6))) (.branch 49 (.leaf (4)) (.leaf (8))))))))
  code := certificateP9_6171
  counts := ![(.branch 21 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 26 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 41 (.leaf (8)) (.branch 46 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 43 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 48 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-19)) (.leaf (-20)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 20 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (-23)) (.leaf (-25)))),
  (.leaf (0))]
  high := ![(.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 36 (.leaf (-20)) (.branch 45 (.leaf (-18)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-12))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 48 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3)))),
  (.branch 41 (.leaf (-5)) (.leaf (-3))),
  (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.leaf (-2)) (.leaf (-1))),
  (.branch 45 (.branch 43 (.branch 26 (.leaf (-25)) (.leaf (-24))) (.branch 44 (.leaf (-21)) (.leaf (-18)))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-12))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (0))]
def witnessP9_313_6172 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (8)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (6)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (7)) (.branch 17 (.leaf (3)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (8)) (.leaf (4))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (6)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (7)) (.branch 33 (.leaf (0)) (.leaf (2)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (5)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (4)) (.branch 39 (.leaf (1)) (.leaf (0)))) (.branch 41 (.leaf (8)) (.branch 42 (.leaf (3)) (.leaf (1))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (6)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (7)) (.leaf (4))))))))
  code := certificateP9_6172
  counts := ![(.branch 22 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.branch 36 (.leaf (-17)) (.leaf (-18))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))) (.branch 14 (.leaf (-15)) (.branch 18 (.leaf (-16)) (.leaf (-17))))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-41))),
  (.branch 12 (.leaf (0)) (.branch 28 (.leaf (-14)) (.leaf (-16)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (-2)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-29)))]
  high := ![(.branch 48 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 44 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-6))) (.branch 49 (.leaf (-4)) (.leaf (-2)))),
  (.branch 45 (.branch 43 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-14)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (0)),
  (.branch 42 (.branch 38 (.branch 4 (.leaf (-41)) (.branch 21 (.leaf (-40)) (.leaf (-39)))) (.branch 40 (.branch 39 (.leaf (-36)) (.leaf (-33))) (.branch 41 (.leaf (-30)) (.leaf (-27))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-24)) (.leaf (-21))) (.branch 45 (.leaf (-18)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 47 (.branch 29 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 33 (.leaf (-4)) (.leaf (-3))),
  (.branch 44 (.branch 25 (.branch 8 (.leaf (-29)) (.leaf (-28))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-24)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))))]
def witnessP9_313_6173 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (6)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (4)) (.leaf (8))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (2)) (.leaf (4))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (6)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (7))))) (.branch 34 (.branch 32 (.leaf (2)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 35 (.leaf (4)) (.branch 36 (.leaf (5)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (3)) (.branch 39 (.leaf (1)) (.leaf (0)))) (.branch 41 (.leaf (2)) (.branch 42 (.leaf (4)) (.leaf (8))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (6)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (3)) (.leaf (0))) (.branch 49 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_6173
  counts := ![(.branch 23 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 48 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 40 (.leaf (-15)) (.leaf (-16)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 14 (.leaf (-18)) (.leaf (-19)))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-9)) (.leaf (-10)))),
  (.branch 25 (.branch 17 (.leaf (0)) (.leaf (-1))) (.branch 42 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 36 (.leaf (-41)) (.leaf (-42)))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 6 (.leaf (0)) (.leaf (-19))),
  (.branch 18 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 45 (.branch 41 (.leaf (-16)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 47 (.branch 40 (.leaf (-19)) (.leaf (-16))) (.branch 48 (.leaf (-12)) (.branch 49 (.leaf (-8)) (.leaf (-4))))),
  (.branch 33 (.leaf (-4)) (.leaf (-3))),
  (.branch 39 (.branch 30 (.leaf (-10)) (.leaf (-9))) (.branch 48 (.leaf (-8)) (.branch 49 (.leaf (-6)) (.leaf (-4))))),
  (.branch 44 (.branch 43 (.leaf (-3)) (.leaf (-2))) (.branch 45 (.leaf (-1)) (.leaf (0)))),
  (.branch 43 (.branch 39 (.branch 37 (.leaf (-42)) (.branch 38 (.leaf (-39)) (.leaf (-36)))) (.branch 41 (.branch 40 (.leaf (-33)) (.leaf (-30))) (.branch 42 (.leaf (-27)) (.leaf (-24))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-18)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 46 (.branch 12 (.leaf (-17)) (.branch 29 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 40 (.branch 35 (.branch 33 (.branch 32 (.leaf (-19)) (.leaf (-18))) (.branch 34 (.leaf (-17)) (.leaf (-16)))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-14))) (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-12)) (.leaf (-11)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-8)) (.branch 44 (.leaf (-7)) (.leaf (-6))))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_313_6174 : CycleWitness 9 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (7)) (.branch 11 (.leaf (5)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (8)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (4)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (5)) (.leaf (7))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (6)))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (0)) (.leaf (3))))) (.branch 34 (.branch 32 (.leaf (4)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 35 (.leaf (8)) (.branch 36 (.leaf (5)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (2)) (.branch 39 (.leaf (1)) (.leaf (0)))) (.branch 41 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (3))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (4)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (5)) (.leaf (8))))))))
  code := certificateP9_6174
  counts := ![(.branch 23 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 48 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 40 (.leaf (-15)) (.leaf (-16)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 14 (.leaf (-18)) (.leaf (-19)))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (-7)) (.leaf (-9)))),
  (.leaf (0))]
  high := ![(.branch 45 (.branch 41 (.leaf (-16)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 47 (.branch 40 (.leaf (-19)) (.leaf (-16))) (.branch 48 (.leaf (-12)) (.branch 49 (.leaf (-8)) (.leaf (-4))))),
  (.branch 39 (.branch 30 (.leaf (-10)) (.leaf (-9))) (.branch 48 (.leaf (-8)) (.branch 49 (.leaf (-6)) (.leaf (-4))))),
  (.branch 46 (.branch 44 (.leaf (-14)) (.branch 45 (.leaf (-12)) (.leaf (-10)))) (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-6))) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 33 (.leaf (-11)) (.branch 46 (.leaf (-10)) (.leaf (-8)))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 37 (.leaf (-3)) (.leaf (-2))),
  (.branch 45 (.branch 42 (.branch 29 (.leaf (-19)) (.leaf (-18))) (.branch 43 (.leaf (-16)) (.branch 44 (.leaf (-14)) (.leaf (-12))))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (0))]
def witnessP9_313 : Fin 59 → CycleWitness 9 := ![witnessP9_313_6116, witnessP9_313_6117, witnessP9_313_6118, witnessP9_313_6119, witnessP9_313_6120, witnessP9_313_6121, witnessP9_313_6122, witnessP9_313_6123, witnessP9_313_6124, witnessP9_313_6125, witnessP9_313_6126, witnessP9_313_6127, witnessP9_313_6128, witnessP9_313_6129, witnessP9_313_6130, witnessP9_313_6131, witnessP9_313_6132, witnessP9_313_6133, witnessP9_313_6134, witnessP9_313_6135, witnessP9_313_6136, witnessP9_313_6137, witnessP9_313_6138, witnessP9_313_6139, witnessP9_313_6140, witnessP9_313_6141, witnessP9_313_6142, witnessP9_313_6143, witnessP9_313_6144, witnessP9_313_6145, witnessP9_313_6146, witnessP9_313_6147, witnessP9_313_6148, witnessP9_313_6149, witnessP9_313_6150, witnessP9_313_6151, witnessP9_313_6152, witnessP9_313_6153, witnessP9_313_6154, witnessP9_313_6155, witnessP9_313_6156, witnessP9_313_6157, witnessP9_313_6158, witnessP9_313_6159, witnessP9_313_6160, witnessP9_313_6161, witnessP9_313_6162, witnessP9_313_6163, witnessP9_313_6164, witnessP9_313_6165, witnessP9_313_6166, witnessP9_313_6167, witnessP9_313_6168, witnessP9_313_6169, witnessP9_313_6170, witnessP9_313_6171, witnessP9_313_6172, witnessP9_313_6173, witnessP9_313_6174]
end RealPinwheel.FiveSixths


