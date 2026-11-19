-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_293
-- name    : RealPinwheel_FiveSixths_WitnessP9_293
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:18:53.727191+00:00
-- url     : https://prove2.me/theorems/58b4c1f1-d4b3-4eba-a7a8-80f5d7a87093
-- title:
--   Exact witness block P9_293
-- statement:
--   These exact witnesses represent words 5078 through 5123 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 5078–5123; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_293_5077 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (4))) (.branch 15 (.leaf (0)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (6))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (4))) (.branch 31 (.leaf (0)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (0))) (.branch 39 (.leaf (1)) (.leaf (3))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (7))) (.branch 43 (.leaf (2)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (4))) (.branch 47 (.leaf (0)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (3))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (8))) (.branch 59 (.leaf (2)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (4))) (.branch 63 (.leaf (0)) (.leaf (3))))))))
  code := certificateP9_5077
  counts := ![(.branch 31 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14)))) (.branch 41 (.leaf (15)) (.branch 44 (.leaf (16)) (.leaf (17))))) (.branch 54 (.branch 49 (.leaf (18)) (.branch 52 (.leaf (19)) (.leaf (20)))) (.branch 60 (.branch 57 (.leaf (21)) (.leaf (22))) (.branch 63 (.leaf (23)) (.leaf (24))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1))),
  (.branch 58 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-54))),
  (.branch 26 (.leaf (0)) (.leaf (-38))),
  (.branch 42 (.leaf (0)) (.leaf (-22))),
  (.branch 58 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 58 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 61 (.leaf (-4)) (.leaf (-3)))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 54 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 23 (.branch 16 (.branch 13 (.branch 11 (.leaf (-54)) (.branch 12 (.leaf (-53)) (.leaf (-52)))) (.branch 14 (.leaf (-51)) (.branch 15 (.leaf (-50)) (.leaf (-49))))) (.branch 19 (.branch 17 (.leaf (-48)) (.branch 18 (.leaf (-47)) (.leaf (-46)))) (.branch 21 (.branch 20 (.leaf (-45)) (.leaf (-44))) (.branch 22 (.leaf (-43)) (.leaf (-42)))))) (.branch 30 (.branch 26 (.branch 24 (.leaf (-41)) (.branch 25 (.leaf (-40)) (.leaf (-39)))) (.branch 28 (.branch 27 (.leaf (-38)) (.leaf (-37))) (.branch 29 (.leaf (-36)) (.leaf (-35))))) (.branch 33 (.branch 31 (.leaf (-34)) (.branch 32 (.leaf (-33)) (.leaf (-32)))) (.branch 35 (.branch 34 (.leaf (-31)) (.leaf (-30))) (.branch 36 (.leaf (-29)) (.leaf (-28))))))) (.branch 50 (.branch 43 (.branch 40 (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19)))) (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 45 (.branch 35 (.branch 30 (.branch 28 (.branch 27 (.leaf (-38)) (.leaf (-37))) (.branch 29 (.leaf (-36)) (.leaf (-35)))) (.branch 32 (.branch 31 (.leaf (-34)) (.leaf (-33))) (.branch 33 (.leaf (-32)) (.branch 34 (.leaf (-31)) (.leaf (-30)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-29)) (.leaf (-28))) (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-25))))) (.branch 42 (.branch 41 (.leaf (-24)) (.leaf (-23))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))))) (.branch 54 (.branch 49 (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 53 (.branch 47 (.branch 44 (.branch 43 (.leaf (-22)) (.leaf (-21))) (.branch 45 (.leaf (-20)) (.branch 46 (.leaf (-19)) (.leaf (-18))))) (.branch 50 (.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_293_5078 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (7)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (7))) (.branch 23 (.leaf (0)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 31 (.leaf (8)) (.leaf (6))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (5)) (.leaf (0))) (.branch 39 (.leaf (7)) (.leaf (3))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (4)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (8)) (.leaf (2))) (.branch 47 (.leaf (0)) (.leaf (6)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (5)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (7))) (.branch 55 (.leaf (0)) (.leaf (4))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (2)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (5))) (.branch 63 (.leaf (8)) (.leaf (6))))))))
  code := certificateP9_5078
  counts := ![(.branch 29 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (11)) (.branch 36 (.leaf (12)) (.leaf (13)))) (.branch 41 (.leaf (14)) (.branch 44 (.leaf (15)) (.leaf (16))))) (.branch 55 (.branch 51 (.leaf (17)) (.branch 53 (.leaf (18)) (.leaf (19)))) (.branch 59 (.leaf (20)) (.branch 61 (.leaf (21)) (.leaf (22))))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 62 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-3)) (.branch 55 (.leaf (-4)) (.leaf (-5))))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 28 (.branch 8 (.leaf (0)) (.leaf (-7))) (.branch 60 (.leaf (-13)) (.leaf (-18)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-39)) (.leaf (-43)))),
  (.branch 11 (.leaf (0)) (.branch 49 (.leaf (-9)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (-9)) (.leaf (-10)))),
  (.branch 13 (.leaf (0)) (.branch 45 (.leaf (-4)) (.leaf (-6))))]
  high := ![(.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3)))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.branch 47 (.branch 36 (.leaf (-23)) (.leaf (-22))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 62 (.branch 61 (.leaf (-18)) (.leaf (-16))) (.branch 63 (.leaf (-14)) (.leaf (-12)))),
  (.branch 58 (.branch 31 (.branch 18 (.leaf (-43)) (.leaf (-42))) (.branch 44 (.leaf (-41)) (.branch 57 (.leaf (-40)) (.leaf (-35))))) (.branch 61 (.branch 59 (.leaf (-30)) (.branch 60 (.leaf (-25)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 50 (.leaf (-11)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.leaf (-6)) (.leaf (-5)))]
def witnessP9_293_5079 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (8)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (3))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (2)) (.leaf (4)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (6)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (3))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (4)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (7)) (.leaf (3))))))))
  code := certificateP9_5079
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1))),
  (.branch 63 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.branch 10 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 15 (.leaf (0)) (.leaf (-49))),
  (.branch 47 (.leaf (0)) (.leaf (-17))),
  (.branch 63 (.leaf (0)) (.leaf (-1))),
  (.branch 31 (.leaf (0)) (.leaf (-33)))]
  high := ![(.branch 59 (.leaf (-14)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 27 (.branch 21 (.branch 18 (.branch 16 (.leaf (-49)) (.branch 17 (.leaf (-48)) (.leaf (-47)))) (.branch 19 (.leaf (-46)) (.branch 20 (.leaf (-45)) (.leaf (-44))))) (.branch 24 (.branch 22 (.leaf (-43)) (.branch 23 (.leaf (-42)) (.leaf (-41)))) (.branch 25 (.leaf (-40)) (.branch 26 (.leaf (-39)) (.leaf (-38)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-37)) (.branch 29 (.leaf (-36)) (.leaf (-35)))) (.branch 31 (.leaf (-34)) (.branch 32 (.leaf (-33)) (.leaf (-32))))) (.branch 36 (.branch 34 (.leaf (-31)) (.branch 35 (.leaf (-30)) (.leaf (-29)))) (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26))))))) (.branch 51 (.branch 45 (.branch 42 (.branch 40 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-23)))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))) (.branch 48 (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17)))) (.branch 49 (.leaf (-16)) (.branch 50 (.leaf (-15)) (.leaf (-14)))))) (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 55 (.branch 51 (.branch 49 (.branch 48 (.leaf (-17)) (.leaf (-16))) (.branch 50 (.leaf (-15)) (.leaf (-14)))) (.branch 53 (.branch 52 (.leaf (-13)) (.leaf (-12))) (.branch 54 (.leaf (-11)) (.leaf (-10))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1)),
  (.branch 47 (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (-33)) (.leaf (-32))) (.branch 34 (.leaf (-31)) (.leaf (-30)))) (.branch 37 (.branch 36 (.leaf (-29)) (.leaf (-28))) (.branch 38 (.leaf (-27)) (.leaf (-26))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-25)) (.leaf (-24))) (.branch 42 (.leaf (-23)) (.leaf (-22)))) (.branch 45 (.branch 44 (.leaf (-21)) (.leaf (-20))) (.branch 46 (.leaf (-19)) (.leaf (-18)))))) (.branch 55 (.branch 51 (.branch 49 (.branch 48 (.leaf (-17)) (.leaf (-16))) (.branch 50 (.leaf (-15)) (.leaf (-14)))) (.branch 53 (.branch 52 (.leaf (-13)) (.leaf (-12))) (.branch 54 (.leaf (-11)) (.leaf (-10))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_293_5080 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (7)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (8))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (3)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (1))) (.branch 47 (.leaf (0)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (5)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (3)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (4)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (6)) (.leaf (1))) (.branch 63 (.leaf (0)) (.leaf (3))))))))
  code := certificateP9_5080
  counts := ![(.branch 31 (.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))) (.branch 47 (.branch 39 (.branch 33 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14)))) (.branch 41 (.leaf (15)) (.branch 44 (.leaf (16)) (.leaf (17))))) (.branch 55 (.branch 49 (.leaf (18)) (.branch 52 (.leaf (19)) (.leaf (20)))) (.branch 60 (.branch 57 (.leaf (21)) (.leaf (22))) (.branch 63 (.leaf (23)) (.leaf (24))))))),
  (.branch 30 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 61 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-23)) (.leaf (-25)))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (-40)) (.leaf (-41)))),
  (.branch 61 (.leaf (0)) (.leaf (-3))),
  (.branch 19 (.leaf (0)) (.leaf (-45))),
  (.branch 40 (.leaf (0)) (.leaf (-24)))]
  high := ![(.branch 58 (.leaf (-5)) (.branch 61 (.leaf (-4)) (.leaf (-3)))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 59 (.branch 57 (.branch 46 (.leaf (-25)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 54 (.leaf (-1)) (.leaf (0))),
  (.branch 60 (.branch 38 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.branch 53 (.branch 30 (.leaf (-41)) (.branch 52 (.leaf (-39)) (.leaf (-36)))) (.branch 55 (.branch 54 (.leaf (-33)) (.leaf (-30))) (.branch 56 (.leaf (-27)) (.leaf (-24))))) (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 41 (.branch 30 (.branch 24 (.branch 21 (.branch 20 (.leaf (-45)) (.leaf (-44))) (.branch 22 (.leaf (-43)) (.branch 23 (.leaf (-42)) (.leaf (-41))))) (.branch 27 (.branch 25 (.leaf (-40)) (.branch 26 (.leaf (-39)) (.leaf (-38)))) (.branch 28 (.leaf (-37)) (.branch 29 (.leaf (-36)) (.leaf (-35)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-34)) (.leaf (-33))) (.branch 33 (.leaf (-32)) (.branch 34 (.leaf (-31)) (.leaf (-30))))) (.branch 38 (.branch 36 (.leaf (-29)) (.branch 37 (.leaf (-28)) (.leaf (-27)))) (.branch 39 (.leaf (-26)) (.branch 40 (.leaf (-25)) (.leaf (-24))))))) (.branch 52 (.branch 46 (.branch 43 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))))) (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 52 (.branch 46 (.branch 43 (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22)))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))))) (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_293_5081 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (7)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (6)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (3))) (.branch 39 (.leaf (0)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (0))) (.branch 43 (.leaf (5)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (8)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (0))) (.branch 59 (.leaf (5)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (6)) (.leaf (3))))))))
  code := certificateP9_5081
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 38 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.leaf (0)) (.branch 63 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.branch 10 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 28 (.leaf (-19)) (.leaf (-20)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 31 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-49))),
  (.branch 47 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 59 (.leaf (-14)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 45 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (0)))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 39 (.branch 27 (.branch 21 (.branch 18 (.branch 16 (.leaf (-49)) (.branch 17 (.leaf (-48)) (.leaf (-47)))) (.branch 19 (.leaf (-46)) (.branch 20 (.leaf (-45)) (.leaf (-44))))) (.branch 24 (.branch 22 (.leaf (-43)) (.branch 23 (.leaf (-42)) (.leaf (-41)))) (.branch 25 (.leaf (-40)) (.branch 26 (.leaf (-39)) (.leaf (-38)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-37)) (.branch 29 (.leaf (-36)) (.leaf (-35)))) (.branch 31 (.leaf (-34)) (.branch 32 (.leaf (-33)) (.leaf (-32))))) (.branch 36 (.branch 34 (.leaf (-31)) (.branch 35 (.leaf (-30)) (.leaf (-29)))) (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26))))))) (.branch 51 (.branch 45 (.branch 42 (.branch 40 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-23)))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))) (.branch 48 (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17)))) (.branch 49 (.leaf (-16)) (.branch 50 (.leaf (-15)) (.leaf (-14)))))) (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 55 (.branch 51 (.branch 49 (.branch 48 (.leaf (-17)) (.leaf (-16))) (.branch 50 (.leaf (-15)) (.leaf (-14)))) (.branch 53 (.branch 52 (.leaf (-13)) (.leaf (-12))) (.branch 54 (.leaf (-11)) (.leaf (-10))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_293_5082 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (3)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (3))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (4))) (.branch 27 (.leaf (7)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (3)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (3))) (.branch 39 (.leaf (1)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (5))) (.branch 43 (.leaf (6)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (2))) (.branch 47 (.leaf (3)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (3))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (2)) (.leaf (4))) (.branch 59 (.leaf (8)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (2))) (.branch 63 (.leaf (3)) (.leaf (5))))))))
  code := certificateP9_5082
  counts := ![(.branch 29 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 36 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 59 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-17)) (.leaf (-18)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-21))),
  (.branch 27 (.leaf (0)) (.leaf (-37))),
  (.branch 59 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 62 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 52 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 43 (.leaf (-2)) (.branch 54 (.leaf (-1)) (.leaf (0)))),
  (.branch 53 (.branch 48 (.branch 45 (.branch 44 (.leaf (-21)) (.leaf (-20))) (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17))))) (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 36 (.branch 31 (.branch 29 (.branch 28 (.leaf (-37)) (.leaf (-36))) (.branch 30 (.leaf (-35)) (.leaf (-34)))) (.branch 33 (.branch 32 (.leaf (-33)) (.leaf (-32))) (.branch 34 (.leaf (-31)) (.branch 35 (.leaf (-30)) (.leaf (-29)))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 42 (.branch 41 (.leaf (-24)) (.leaf (-23))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))))) (.branch 54 (.branch 49 (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_293_5083 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (7))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (8))) (.branch 31 (.leaf (2)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (3)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (2))) (.branch 39 (.leaf (1)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (6)) (.leaf (3))) (.branch 43 (.leaf (0)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (7))) (.branch 47 (.leaf (0)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (3))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (4)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (8))) (.branch 63 (.leaf (3)) (.leaf (6))))))))
  code := certificateP9_5083
  counts := ![(.branch 29 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 47 (.branch 36 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.branch 43 (.leaf (12)) (.leaf (13))))) (.branch 54 (.branch 51 (.leaf (14)) (.leaf (15))) (.branch 58 (.leaf (16)) (.branch 61 (.leaf (17)) (.leaf (18))))))),
  (.branch 28 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 59 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 63 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.branch 62 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-23))) (.branch 11 (.leaf (-28)) (.leaf (-29)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 31 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-37))) (.branch 17 (.leaf (-38)) (.branch 24 (.leaf (-39)) (.leaf (-40))))) (.branch 45 (.branch 38 (.leaf (-41)) (.leaf (-42))) (.branch 52 (.leaf (-43)) (.branch 59 (.leaf (-44)) (.leaf (-45)))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-10))) (.branch 20 (.leaf (-11)) (.branch 27 (.leaf (-12)) (.leaf (-13))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (-6))) (.branch 57 (.leaf (-8)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 21 (.leaf (0)) (.branch 41 (.leaf (-1)) (.leaf (-3)))),
  (.branch 14 (.leaf (0)) (.leaf (-18))),
  (.branch 30 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 62 (.branch 44 (.leaf (-29)) (.leaf (-27))) (.branch 63 (.leaf (-18)) (.leaf (-9)))),
  (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 60 (.leaf (-45)) (.leaf (-36))) (.branch 62 (.leaf (-27)) (.branch 63 (.leaf (-18)) (.leaf (-9))))),
  (.branch 28 (.leaf (-13)) (.leaf (-9))),
  (.branch 60 (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7)))) (.branch 62 (.branch 61 (.leaf (-6)) (.leaf (-5))) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 61 (.branch 59 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 43 (.branch 42 (.leaf (-3)) (.leaf (-2))) (.branch 44 (.leaf (-1)) (.leaf (0)))),
  (.branch 55 (.branch 50 (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 52 (.branch 51 (.leaf (-14)) (.leaf (-13))) (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_293_5084 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (7)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (4)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (2))) (.branch 23 (.leaf (8)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (5)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (3))) (.branch 39 (.leaf (7)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (2))) (.branch 43 (.leaf (6)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (3)) (.leaf (1))) (.branch 47 (.leaf (4)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (2))) (.branch 55 (.leaf (8)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (4)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (1))) (.branch 63 (.leaf (6)) (.leaf (3))))))))
  code := certificateP9_5084
  counts := ![(.branch 28 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 38 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 43 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 18 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 34 (.leaf (-8)) (.branch 50 (.leaf (-9)) (.leaf (-10))))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-17)) (.leaf (-18)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (-6))) (.branch 47 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.branch 31 (.leaf (-21)) (.leaf (-24)))),
  (.branch 21 (.leaf (0)) (.branch 63 (.leaf (-1)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-25))),
  (.branch 23 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-8)) (.leaf (-6)))),
  (.branch 62 (.branch 55 (.leaf (-18)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 39 (.leaf (-2)) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.branch 61 (.branch 48 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 58 (.branch 55 (.branch 32 (.leaf (-24)) (.branch 54 (.leaf (-23)) (.leaf (-21)))) (.branch 56 (.leaf (-19)) (.branch 57 (.leaf (-17)) (.leaf (-15))))) (.branch 61 (.branch 59 (.leaf (-13)) (.branch 60 (.leaf (-11)) (.leaf (-9)))) (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-5)) (.leaf (-3)))))),
  (.leaf (-3)),
  (.branch 51 (.branch 45 (.branch 42 (.branch 40 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-23)))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))) (.branch 48 (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17)))) (.branch 49 (.leaf (-16)) (.branch 50 (.leaf (-15)) (.leaf (-14)))))) (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_293_5085 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (8)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (7)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (5)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (8))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (4))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (7)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (1))) (.branch 47 (.leaf (0)) (.leaf (5)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (8)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (6)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (4)) (.leaf (1))) (.branch 63 (.leaf (0)) (.leaf (7))))))))
  code := certificateP9_5085
  counts := ![(.branch 31 (.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))) (.branch 47 (.branch 39 (.branch 33 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14)))) (.branch 41 (.leaf (15)) (.branch 44 (.leaf (16)) (.leaf (17))))) (.branch 55 (.branch 49 (.leaf (18)) (.branch 52 (.leaf (19)) (.leaf (20)))) (.branch 60 (.branch 57 (.leaf (21)) (.leaf (22))) (.branch 63 (.leaf (23)) (.leaf (24))))))),
  (.branch 30 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 43 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-23)) (.leaf (-25)))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (-40)) (.leaf (-41)))),
  (.branch 40 (.branch 19 (.leaf (0)) (.leaf (-7))) (.branch 61 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.leaf (-49))),
  (.branch 16 (.leaf (0)) (.branch 37 (.leaf (-16)) (.leaf (-17)))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 32 (.branch 11 (.leaf (0)) (.leaf (-31))) (.branch 53 (.leaf (-32)) (.leaf (-33))))]
  high := ![(.branch 58 (.leaf (-5)) (.branch 61 (.leaf (-4)) (.leaf (-3)))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 59 (.branch 57 (.branch 46 (.leaf (-25)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 57 (.branch 53 (.branch 30 (.leaf (-41)) (.branch 52 (.leaf (-39)) (.leaf (-36)))) (.branch 55 (.branch 54 (.leaf (-33)) (.leaf (-30))) (.branch 56 (.leaf (-27)) (.leaf (-24))))) (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 55 (.branch 51 (.branch 49 (.branch 6 (.leaf (-49)) (.leaf (-48))) (.branch 50 (.leaf (-45)) (.leaf (-42)))) (.branch 53 (.branch 52 (.leaf (-39)) (.leaf (-36))) (.branch 54 (.leaf (-33)) (.leaf (-30))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-27)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 61 (.branch 38 (.leaf (-17)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.leaf (-1)) (.leaf (0))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-33)) (.leaf (-30))) (.branch 56 (.leaf (-27)) (.branch 57 (.leaf (-24)) (.leaf (-21))))) (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))))]
def witnessP9_293_5086 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (2))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (3)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (3))) (.branch 39 (.leaf (1)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (4)) (.leaf (2))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (8)) (.leaf (2))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (4)) (.leaf (3))) (.branch 59 (.leaf (0)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (3)) (.leaf (4))))))))
  code := certificateP9_5086
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 40 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 56 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 38 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 16 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1))),
  (.branch 53 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 47 (.leaf (-9)) (.leaf (-10)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 31 (.leaf (-2)) (.branch 63 (.leaf (-3)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-59))),
  (.branch 21 (.leaf (0)) (.leaf (-43))),
  (.branch 37 (.leaf (0)) (.leaf (-27))),
  (.branch 53 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 53 (.leaf (-12)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.branch 61 (.leaf (-10)) (.leaf (-8))) (.branch 63 (.leaf (-6)) (.leaf (-4)))),
  (.leaf (-4)),
  (.leaf (0)),
  (.branch 34 (.branch 19 (.branch 12 (.branch 8 (.branch 6 (.leaf (-59)) (.branch 7 (.leaf (-58)) (.leaf (-57)))) (.branch 10 (.branch 9 (.leaf (-56)) (.leaf (-55))) (.branch 11 (.leaf (-54)) (.leaf (-53))))) (.branch 15 (.branch 13 (.leaf (-52)) (.branch 14 (.leaf (-51)) (.leaf (-50)))) (.branch 17 (.branch 16 (.leaf (-49)) (.leaf (-48))) (.branch 18 (.leaf (-47)) (.leaf (-46)))))) (.branch 26 (.branch 22 (.branch 20 (.leaf (-45)) (.branch 21 (.leaf (-44)) (.leaf (-43)))) (.branch 24 (.branch 23 (.leaf (-42)) (.leaf (-41))) (.branch 25 (.leaf (-40)) (.leaf (-39))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-38)) (.leaf (-37))) (.branch 29 (.leaf (-36)) (.leaf (-35)))) (.branch 32 (.branch 31 (.leaf (-34)) (.leaf (-33))) (.branch 33 (.leaf (-32)) (.leaf (-31))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.leaf (-30)) (.branch 36 (.leaf (-29)) (.leaf (-28)))) (.branch 39 (.branch 38 (.leaf (-27)) (.leaf (-26))) (.branch 40 (.leaf (-25)) (.leaf (-24))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 44 (.leaf (-21)) (.leaf (-20)))) (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))))) (.branch 56 (.branch 52 (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (-43)) (.leaf (-42))) (.branch 24 (.leaf (-41)) (.branch 25 (.leaf (-40)) (.leaf (-39))))) (.branch 28 (.branch 27 (.leaf (-38)) (.leaf (-37))) (.branch 29 (.leaf (-36)) (.branch 30 (.leaf (-35)) (.leaf (-34)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-33)) (.leaf (-32))) (.branch 34 (.leaf (-31)) (.branch 35 (.leaf (-30)) (.leaf (-29))))) (.branch 39 (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26)))) (.branch 40 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-23))))))) (.branch 53 (.branch 47 (.branch 44 (.branch 43 (.leaf (-22)) (.leaf (-21))) (.branch 45 (.leaf (-20)) (.branch 46 (.leaf (-19)) (.leaf (-18))))) (.branch 50 (.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 50 (.branch 43 (.branch 40 (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19)))) (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_293_5087 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (6))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (7)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (8)) (.leaf (4))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (5))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (6)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (4))) (.branch 39 (.leaf (1)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (3)) (.leaf (8))) (.branch 43 (.leaf (0)) (.leaf (2)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (5)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (6)) (.leaf (4))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (7))) (.branch 59 (.leaf (0)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (8)) (.leaf (3))))))))
  code := certificateP9_5087
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 40 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 56 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 16 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 26 (.branch 5 (.leaf (0)) (.leaf (-49))) (.branch 47 (.leaf (-50)) (.leaf (-51)))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (-34)) (.leaf (-35)))),
  (.branch 15 (.leaf (0)) (.leaf (-19))),
  (.branch 42 (.branch 21 (.leaf (0)) (.leaf (-1))) (.branch 63 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 53 (.leaf (-12)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 55 (.branch 51 (.branch 49 (.branch 48 (.leaf (-51)) (.leaf (-48))) (.branch 50 (.leaf (-45)) (.leaf (-42)))) (.branch 53 (.branch 52 (.leaf (-39)) (.leaf (-36))) (.branch 54 (.leaf (-33)) (.leaf (-30))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-27)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 58 (.branch 55 (.branch 32 (.leaf (-35)) (.branch 54 (.leaf (-33)) (.leaf (-30)))) (.branch 56 (.leaf (-27)) (.branch 57 (.leaf (-24)) (.leaf (-21))))) (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 60 (.branch 16 (.leaf (-19)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3))]
def witnessP9_293_5088 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (7)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (3))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (0))) (.branch 43 (.leaf (1)) (.leaf (5)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (2))) (.branch 47 (.leaf (1)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (8)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (3))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (1)) (.leaf (5)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (2))) (.branch 63 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_5088
  counts := ![(.branch 29 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 45 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 61 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 59 (.leaf (14)) (.branch 63 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 53 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-27))),
  (.branch 21 (.leaf (0)) (.leaf (-43))),
  (.branch 53 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 52 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 50 (.branch 43 (.branch 40 (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19)))) (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (-43)) (.leaf (-42))) (.branch 24 (.leaf (-41)) (.branch 25 (.leaf (-40)) (.leaf (-39))))) (.branch 28 (.branch 27 (.leaf (-38)) (.leaf (-37))) (.branch 29 (.leaf (-36)) (.branch 30 (.leaf (-35)) (.leaf (-34)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-33)) (.leaf (-32))) (.branch 34 (.leaf (-31)) (.branch 35 (.leaf (-30)) (.leaf (-29))))) (.branch 39 (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26)))) (.branch 40 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-23))))))) (.branch 53 (.branch 47 (.branch 44 (.branch 43 (.leaf (-22)) (.leaf (-21))) (.branch 45 (.leaf (-20)) (.branch 46 (.leaf (-19)) (.leaf (-18))))) (.branch 50 (.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_293_5089 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (7))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (6)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (8)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (5)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (7))) (.branch 43 (.leaf (0)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (3)) (.leaf (0))) (.branch 47 (.leaf (5)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (6)) (.leaf (4)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (0))) (.branch 59 (.leaf (1)) (.leaf (8)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (0))) (.branch 63 (.leaf (5)) (.leaf (4))))))))
  code := certificateP9_5089
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 40 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 56 (.branch 50 (.leaf (15)) (.branch 53 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 60 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 26 (.leaf (-18)) (.branch 58 (.leaf (-25)) (.leaf (-31))))),
  (.branch 27 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-6)) (.leaf (-7)))) (.branch 49 (.branch 38 (.leaf (-9)) (.leaf (-10))) (.branch 59 (.leaf (-11)) (.leaf (-13))))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-17)) (.leaf (-19)))),
  (.branch 32 (.branch 7 (.leaf (0)) (.leaf (-6))) (.branch 57 (.leaf (-7)) (.leaf (-8)))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (-12))) (.branch 51 (.leaf (-15)) (.leaf (-17)))),
  (.branch 10 (.leaf (0)) (.leaf (-22))),
  (.branch 28 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 59 (.leaf (-31)) (.branch 63 (.leaf (-26)) (.leaf (-19)))),
  (.branch 61 (.branch 60 (.leaf (-13)) (.leaf (-12))) (.branch 62 (.leaf (-11)) (.branch 63 (.leaf (-10)) (.leaf (-9))))),
  (.branch 55 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 60 (.branch 58 (.leaf (-8)) (.branch 59 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.branch 61 (.leaf (-5)) (.leaf (-4))) (.branch 63 (.leaf (-3)) (.leaf (-2))))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 57 (.branch 54 (.branch 52 (.leaf (-17)) (.branch 53 (.leaf (-16)) (.leaf (-15)))) (.branch 55 (.leaf (-14)) (.branch 56 (.leaf (-13)) (.leaf (-12))))) (.branch 60 (.branch 58 (.leaf (-11)) (.branch 59 (.leaf (-10)) (.leaf (-9)))) (.branch 62 (.branch 61 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-6)) (.leaf (-5)))))),
  (.branch 53 (.branch 47 (.branch 44 (.branch 43 (.leaf (-22)) (.leaf (-21))) (.branch 45 (.leaf (-20)) (.branch 46 (.leaf (-19)) (.leaf (-18))))) (.branch 50 (.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_293_5090 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (8)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (7)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (4))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (8)) (.leaf (5))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (3)) (.leaf (7))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (4)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (5))) (.branch 39 (.leaf (1)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (8)) (.leaf (2))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (4)) (.leaf (7)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (5)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (6)) (.leaf (2))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (8)) (.leaf (3))) (.branch 59 (.leaf (0)) (.leaf (4)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (5)) (.leaf (7))))))))
  code := certificateP9_5090
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 40 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 56 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-10)) (.leaf (-11)))),
  (.branch 6 (.leaf (0)) (.branch 31 (.leaf (-7)) (.leaf (-8)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (-3))) (.branch 47 (.leaf (-4)) (.leaf (-5)))),
  (.branch 12 (.leaf (0)) (.branch 63 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 53 (.leaf (-12)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 59 (.branch 56 (.branch 55 (.leaf (-11)) (.leaf (-10))) (.branch 57 (.leaf (-9)) (.branch 58 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 60 (.leaf (-6)) (.leaf (-5))) (.branch 62 (.leaf (-4)) (.branch 63 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 60 (.branch 45 (.leaf (-8)) (.branch 59 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.branch 61 (.leaf (-5)) (.leaf (-4))) (.branch 63 (.leaf (-3)) (.leaf (-2))))),
  (.branch 62 (.branch 61 (.leaf (-5)) (.leaf (-4))) (.branch 63 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_293_5091 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (3))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (8)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (2))) (.branch 23 (.leaf (4)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (7)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (5)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (8)) (.leaf (3))) (.branch 39 (.leaf (4)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (2))) (.branch 43 (.leaf (6)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (3)) (.leaf (1))) (.branch 47 (.leaf (7)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (2))) (.branch 55 (.leaf (4)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (8)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (1))) (.branch 63 (.leaf (6)) (.leaf (3))))))))
  code := certificateP9_5091
  counts := ![(.branch 28 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 38 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 43 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 18 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 34 (.leaf (-8)) (.branch 50 (.leaf (-9)) (.leaf (-10))))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-17)) (.leaf (-18)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.branch 31 (.leaf (-21)) (.leaf (-24)))),
  (.branch 21 (.leaf (0)) (.branch 63 (.leaf (-1)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 47 (.leaf (-33)) (.leaf (-35)))),
  (.branch 15 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-8)) (.leaf (-6)))),
  (.branch 62 (.branch 55 (.leaf (-18)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 39 (.leaf (-2)) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 55 (.branch 32 (.leaf (-24)) (.branch 54 (.leaf (-23)) (.leaf (-21)))) (.branch 56 (.leaf (-19)) (.branch 57 (.leaf (-17)) (.leaf (-15))))) (.branch 61 (.branch 59 (.leaf (-13)) (.branch 60 (.leaf (-11)) (.leaf (-9)))) (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-5)) (.leaf (-3)))))),
  (.leaf (-3)),
  (.branch 55 (.branch 51 (.branch 49 (.branch 48 (.leaf (-35)) (.leaf (-33))) (.branch 50 (.leaf (-31)) (.leaf (-29)))) (.branch 53 (.branch 52 (.leaf (-27)) (.leaf (-25))) (.branch 54 (.leaf (-23)) (.leaf (-21))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-19)) (.leaf (-17))) (.branch 58 (.leaf (-15)) (.leaf (-13)))) (.branch 61 (.branch 60 (.leaf (-11)) (.leaf (-9))) (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-5)) (.leaf (-3))))))),
  (.branch 60 (.branch 16 (.leaf (-13)) (.branch 38 (.leaf (-12)) (.leaf (-11)))) (.branch 62 (.branch 61 (.leaf (-9)) (.leaf (-7))) (.branch 63 (.leaf (-5)) (.leaf (-3)))))]
def witnessP9_293_5092 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (6)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (8)) (.leaf (3))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (0))) (.branch 31 (.leaf (1)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (4))) (.branch 39 (.leaf (1)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (6)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (0))) (.branch 47 (.leaf (1)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (5)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (8)) (.leaf (3))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (2)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (4)))) (.branch 62 (.branch 61 (.leaf (6)) (.leaf (0))) (.branch 63 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_5092
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 40 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 56 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 39 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 55 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 63 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 12 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 53 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 45 (.leaf (-9)) (.leaf (-10)))),
  (.branch 32 (.leaf (0)) (.leaf (-1))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (-5))) (.branch 48 (.leaf (-6)) (.leaf (-7)))),
  (.branch 9 (.leaf (0)) (.branch 29 (.leaf (-25)) (.leaf (-28)))),
  (.branch 19 (.leaf (0)) (.branch 61 (.leaf (-5)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-27))),
  (.branch 21 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 53 (.leaf (-12)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 60 (.branch 58 (.branch 46 (.leaf (-10)) (.leaf (-9))) (.branch 59 (.leaf (-8)) (.leaf (-7)))) (.branch 62 (.branch 61 (.leaf (-6)) (.leaf (-5))) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 55 (.leaf (-1)) (.leaf (0))),
  (.branch 61 (.branch 49 (.leaf (-7)) (.leaf (-6))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 57 (.branch 53 (.branch 30 (.leaf (-28)) (.branch 52 (.leaf (-27)) (.leaf (-25)))) (.branch 55 (.branch 54 (.leaf (-23)) (.leaf (-21))) (.branch 56 (.leaf (-19)) (.leaf (-17))))) (.branch 60 (.branch 58 (.leaf (-15)) (.branch 59 (.leaf (-13)) (.leaf (-11)))) (.branch 62 (.branch 61 (.leaf (-9)) (.leaf (-7))) (.branch 63 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-5)) (.leaf (-3)))),
  (.branch 50 (.branch 43 (.branch 40 (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19)))) (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_293_5093 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (7))) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (3)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (8)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (7)) (.leaf (6))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (8))) (.branch 43 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (3)) (.leaf (6)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (7)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (4)) (.leaf (5))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (1)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (8)) (.leaf (6))))))))
  code := certificateP9_5093
  counts := ![(.branch 29 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 59 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-20))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 31 (.branch 10 (.leaf (0)) (.leaf (-34))) (.branch 52 (.leaf (-35)) (.leaf (-36)))),
  (.branch 20 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 61 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 48 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 58 (.branch 55 (.branch 53 (.leaf (-36)) (.branch 54 (.leaf (-33)) (.leaf (-30)))) (.branch 56 (.leaf (-27)) (.branch 57 (.leaf (-24)) (.leaf (-21))))) (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 21 (.leaf (-4)) (.leaf (-3)))]
def witnessP9_293_5094 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (0))) (.branch 15 (.leaf (6)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (1)) (.leaf (8))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (3)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (6)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (5))) (.branch 39 (.leaf (1)) (.leaf (7))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (2))) (.branch 43 (.leaf (3)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (0))) (.branch 47 (.leaf (6)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (5)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (1)) (.leaf (8))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (4))) (.branch 59 (.leaf (3)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (0))) (.branch 63 (.leaf (6)) (.leaf (5))))))))
  code := certificateP9_5094
  counts := ![(.branch 30 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 56 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-17)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-34))),
  (.branch 38 (.leaf (0)) (.leaf (-2))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-24))),
  (.branch 24 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 58 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.branch 55 (.leaf (-18)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.branch 20 (.branch 7 (.leaf (-34)) (.leaf (-33))) (.branch 33 (.leaf (-32)) (.branch 46 (.leaf (-31)) (.leaf (-30))))) (.branch 61 (.branch 60 (.leaf (-25)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 39 (.leaf (-2)) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 52 (.branch 46 (.branch 43 (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22)))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))))) (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_293_5095 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (7))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (2))) (.branch 11 (.leaf (6)) (.leaf (8)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (7)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (3))) (.branch 23 (.leaf (2)) (.leaf (6))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (8)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (5))) (.branch 31 (.leaf (3)) (.leaf (7))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (8))) (.branch 39 (.leaf (0)) (.leaf (3))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (2))) (.branch 43 (.leaf (5)) (.leaf (7)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (0))) (.branch 47 (.leaf (1)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (3)) (.leaf (6))) (.branch 51 (.leaf (8)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (4))) (.branch 55 (.leaf (2)) (.leaf (5))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (7)) (.leaf (3))) (.branch 59 (.leaf (0)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (6))) (.branch 63 (.leaf (4)) (.leaf (8))))))))
  code := certificateP9_5095
  counts := ![(.branch 27 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 33 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.leaf (7))))),
  (.branch 36 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 62 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 7 (.leaf (-27)) (.leaf (-29)))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-22)) (.leaf (-23)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 31 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-36))) (.branch 22 (.leaf (-37)) (.leaf (-38)))) (.branch 49 (.branch 40 (.leaf (-39)) (.leaf (-40))) (.branch 58 (.leaf (-41)) (.leaf (-42))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (-8))) (.branch 26 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.branch 30 (.leaf (-39)) (.leaf (-42)))),
  (.branch 11 (.leaf (0)) (.branch 62 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.branch 44 (.leaf (-34)) (.leaf (-36)))),
  (.branch 12 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 60 (.branch 40 (.leaf (-29)) (.branch 53 (.leaf (-28)) (.leaf (-25)))) (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 61 (.branch 54 (.leaf (-23)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 49 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 61 (.branch 59 (.leaf (-42)) (.branch 60 (.leaf (-35)) (.leaf (-28)))) (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 27 (.leaf (-10)) (.leaf (-7))),
  (.branch 59 (.branch 44 (.branch 31 (.leaf (-42)) (.leaf (-41))) (.branch 57 (.leaf (-40)) (.branch 58 (.leaf (-35)) (.leaf (-30))))) (.branch 61 (.branch 60 (.leaf (-25)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 63 (.leaf (-10)) (.leaf (-5))),
  (.branch 60 (.branch 58 (.branch 45 (.leaf (-36)) (.leaf (-35))) (.branch 59 (.leaf (-30)) (.leaf (-25)))) (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.branch 52 (.leaf (-1)) (.leaf (0)))))]
def witnessP9_293_5096 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (8)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (3))) (.branch 23 (.leaf (7)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (6)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (3)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (0))) (.branch 39 (.leaf (8)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (3)) (.leaf (0))) (.branch 43 (.leaf (5)) (.leaf (2)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (1))) (.branch 47 (.leaf (0)) (.leaf (6)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (4))) (.branch 55 (.leaf (7)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (6)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (4)) (.leaf (5))))))))
  code := certificateP9_5096
  counts := ![(.branch 29 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 57 (.branch 52 (.leaf (11)) (.leaf (12))) (.branch 61 (.leaf (13)) (.leaf (14)))))),
  (.branch 30 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.leaf (7))))),
  (.branch 36 (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 33 (.leaf (-12)) (.branch 42 (.leaf (-13)) (.leaf (-14))))),
  (.branch 18 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 34 (.leaf (-8)) (.branch 50 (.leaf (-9)) (.leaf (-10))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-26)) (.leaf (-27)))) (.branch 49 (.branch 31 (.leaf (-28)) (.leaf (-29))) (.branch 58 (.leaf (-31)) (.leaf (-32))))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (-1))) (.branch 26 (.leaf (-7)) (.leaf (-8)))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 23 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-25)))]
  high := ![(.branch 62 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 63 (.leaf (-10)) (.leaf (-7)))),
  (.branch 57 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-8)) (.leaf (-6)))),
  (.branch 61 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 61 (.branch 59 (.leaf (-32)) (.branch 60 (.leaf (-27)) (.leaf (-22)))) (.branch 62 (.leaf (-17)) (.branch 63 (.leaf (-12)) (.leaf (-7))))),
  (.branch 27 (.leaf (-8)) (.leaf (-7))),
  (.branch 54 (.leaf (-1)) (.leaf (0))),
  (.branch 60 (.branch 38 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 45 (.branch 42 (.branch 40 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-23)))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))) (.branch 48 (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17)))) (.branch 49 (.leaf (-16)) (.branch 50 (.leaf (-15)) (.leaf (-14)))))) (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_293_5097 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (1)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (7))) (.branch 15 (.leaf (0)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (6))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (5))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (8))) (.branch 31 (.leaf (4)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (6))) (.branch 39 (.leaf (1)) (.leaf (4))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (3)) (.leaf (0))) (.branch 43 (.leaf (2)) (.leaf (5)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (7))) (.branch 47 (.leaf (0)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (4)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (2)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (8))) (.branch 63 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_5097
  counts := ![(.branch 28 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 37 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 56 (.branch 52 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 16 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.leaf (7))))),
  (.branch 36 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.branch 62 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 28 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-11)) (.leaf (-13)))) (.branch 37 (.leaf (-14)) (.branch 60 (.leaf (-15)) (.leaf (-16))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-26))) (.branch 21 (.leaf (-32)) (.leaf (-33)))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-6)) (.leaf (-7)))) (.branch 44 (.leaf (-8)) (.branch 53 (.leaf (-10)) (.leaf (-11))))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 14 (.leaf (0)) (.leaf (-18))),
  (.branch 30 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 62 (.branch 61 (.leaf (-16)) (.leaf (-13))) (.branch 63 (.leaf (-10)) (.leaf (-7)))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 60 (.branch 22 (.leaf (-33)) (.branch 59 (.leaf (-32)) (.leaf (-27)))) (.branch 62 (.branch 61 (.leaf (-22)) (.leaf (-17))) (.branch 63 (.leaf (-12)) (.leaf (-7))))),
  (.branch 54 (.leaf (-11)) (.leaf (-7))),
  (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 55 (.branch 50 (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 52 (.branch 51 (.leaf (-14)) (.leaf (-13))) (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_293_5098 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (8)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (3))) (.branch 23 (.leaf (1)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (6)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (1)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (3)) (.leaf (4)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (2))) (.branch 47 (.leaf (1)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (7)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (3))) (.branch 55 (.leaf (1)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (3)) (.leaf (4)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (2))) (.branch 63 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_5098
  counts := ![(.branch 29 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 39 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 55 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 63 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 16 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 38 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-60))),
  (.branch 36 (.leaf (0)) (.leaf (-28))),
  (.branch 52 (.leaf (0)) (.leaf (-12))),
  (.branch 20 (.leaf (0)) (.leaf (-44)))]
  high := ![(.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.leaf (-8)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.branch 19 (.branch 11 (.branch 7 (.branch 5 (.leaf (-60)) (.branch 6 (.leaf (-59)) (.leaf (-58)))) (.branch 9 (.branch 8 (.leaf (-57)) (.leaf (-56))) (.branch 10 (.leaf (-55)) (.leaf (-54))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-53)) (.leaf (-52))) (.branch 14 (.leaf (-51)) (.leaf (-50)))) (.branch 17 (.branch 16 (.leaf (-49)) (.leaf (-48))) (.branch 18 (.leaf (-47)) (.leaf (-46)))))) (.branch 26 (.branch 22 (.branch 20 (.leaf (-45)) (.branch 21 (.leaf (-44)) (.leaf (-43)))) (.branch 24 (.branch 23 (.leaf (-42)) (.leaf (-41))) (.branch 25 (.leaf (-40)) (.leaf (-39))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-38)) (.leaf (-37))) (.branch 29 (.leaf (-36)) (.leaf (-35)))) (.branch 32 (.branch 31 (.leaf (-34)) (.leaf (-33))) (.branch 33 (.leaf (-32)) (.leaf (-31))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.leaf (-30)) (.branch 36 (.leaf (-29)) (.leaf (-28)))) (.branch 39 (.branch 38 (.leaf (-27)) (.leaf (-26))) (.branch 40 (.leaf (-25)) (.leaf (-24))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 44 (.leaf (-21)) (.leaf (-20)))) (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))))) (.branch 56 (.branch 52 (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 50 (.branch 43 (.branch 39 (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26)))) (.branch 41 (.branch 40 (.leaf (-25)) (.leaf (-24))) (.branch 42 (.leaf (-23)) (.leaf (-22))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19)))) (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 31 (.branch 25 (.branch 22 (.branch 21 (.leaf (-44)) (.leaf (-43))) (.branch 23 (.leaf (-42)) (.branch 24 (.leaf (-41)) (.leaf (-40))))) (.branch 28 (.branch 26 (.leaf (-39)) (.branch 27 (.leaf (-38)) (.leaf (-37)))) (.branch 29 (.leaf (-36)) (.branch 30 (.leaf (-35)) (.leaf (-34)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-33)) (.leaf (-32))) (.branch 34 (.leaf (-31)) (.branch 35 (.leaf (-30)) (.leaf (-29))))) (.branch 39 (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26)))) (.branch 40 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-23))))))) (.branch 53 (.branch 47 (.branch 44 (.branch 43 (.leaf (-22)) (.leaf (-21))) (.branch 45 (.leaf (-20)) (.branch 46 (.leaf (-19)) (.leaf (-18))))) (.branch 50 (.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_293_5099 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (4))) (.branch 23 (.leaf (1)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (1)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (4)) (.leaf (8)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (2))) (.branch 47 (.leaf (1)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (5)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (4))) (.branch 55 (.leaf (1)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (3)) (.leaf (6)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (2))) (.branch 63 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_5099
  counts := ![(.branch 29 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 39 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 55 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 63 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.leaf (0)) (.branch 60 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-16)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 28 (.leaf (0)) (.leaf (-4))),
  (.branch 12 (.leaf (0)) (.leaf (-52))),
  (.branch 44 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.leaf (-8)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 49 (.leaf (-16)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 25 (.branch 18 (.branch 15 (.branch 13 (.leaf (-52)) (.branch 14 (.leaf (-51)) (.leaf (-50)))) (.branch 16 (.leaf (-49)) (.branch 17 (.leaf (-48)) (.leaf (-47))))) (.branch 21 (.branch 19 (.leaf (-46)) (.branch 20 (.leaf (-45)) (.leaf (-44)))) (.branch 23 (.branch 22 (.leaf (-43)) (.leaf (-42))) (.branch 24 (.leaf (-41)) (.leaf (-40)))))) (.branch 31 (.branch 28 (.branch 26 (.leaf (-39)) (.branch 27 (.leaf (-38)) (.leaf (-37)))) (.branch 29 (.leaf (-36)) (.branch 30 (.leaf (-35)) (.leaf (-34))))) (.branch 34 (.branch 32 (.leaf (-33)) (.branch 33 (.leaf (-32)) (.leaf (-31)))) (.branch 36 (.branch 35 (.leaf (-30)) (.leaf (-29))) (.branch 37 (.leaf (-28)) (.leaf (-27))))))) (.branch 51 (.branch 44 (.branch 41 (.branch 39 (.leaf (-26)) (.branch 40 (.leaf (-25)) (.leaf (-24)))) (.branch 42 (.leaf (-23)) (.branch 43 (.leaf (-22)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-20)) (.branch 46 (.leaf (-19)) (.leaf (-18)))) (.branch 49 (.branch 48 (.leaf (-17)) (.leaf (-16))) (.branch 50 (.leaf (-15)) (.leaf (-14)))))) (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 54 (.branch 49 (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16))))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_293_5100 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (1)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (7)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (4))) (.branch 39 (.leaf (0)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (3)) (.leaf (2))) (.branch 43 (.leaf (0)) (.leaf (6)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (4))) (.branch 51 (.leaf (1)) (.leaf (5)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (0)) (.leaf (8)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (1))) (.branch 63 (.leaf (0)) (.leaf (3))))))))
  code := certificateP9_5100
  counts := ![(.branch 31 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 53 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 63 (.leaf (19)) (.leaf (20))))))),
  (.branch 30 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 16 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 60 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 23 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 17 (.leaf (-7)) (.leaf (-8)))) (.branch 39 (.branch 33 (.leaf (-10)) (.leaf (-11))) (.branch 49 (.leaf (-13)) (.branch 55 (.leaf (-14)) (.leaf (-16)))))),
  (.branch 2 (.leaf (0)) (.branch 34 (.leaf (-17)) (.leaf (-19)))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 47 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 26 (.branch 6 (.leaf (0)) (.leaf (-11))) (.branch 58 (.leaf (-17)) (.leaf (-22)))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-20))),
  (.branch 28 (.leaf (0)) (.leaf (-36))),
  (.branch 60 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 56 (.leaf (-16)) (.branch 60 (.leaf (-15)) (.leaf (-14)))),
  (.branch 46 (.branch 35 (.leaf (-19)) (.leaf (-18))) (.branch 57 (.leaf (-17)) (.branch 63 (.leaf (-14)) (.leaf (-9))))),
  (.branch 55 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 62 (.leaf (-8)) (.branch 63 (.leaf (-6)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 61 (.branch 59 (.leaf (-22)) (.branch 60 (.leaf (-20)) (.leaf (-18)))) (.branch 62 (.leaf (-16)) (.branch 63 (.leaf (-14)) (.leaf (-12))))),
  (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.branch 49 (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16))))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 37 (.branch 32 (.branch 30 (.branch 29 (.leaf (-36)) (.leaf (-35))) (.branch 31 (.leaf (-34)) (.leaf (-33)))) (.branch 34 (.branch 33 (.leaf (-32)) (.leaf (-31))) (.branch 35 (.leaf (-30)) (.branch 36 (.leaf (-29)) (.leaf (-28)))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-27)) (.leaf (-26))) (.branch 40 (.leaf (-25)) (.leaf (-24)))) (.branch 43 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))))) (.branch 55 (.branch 50 (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 52 (.branch 51 (.leaf (-14)) (.leaf (-13))) (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_293_5101 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (2))) (.branch 11 (.leaf (7)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (5))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (6))) (.branch 19 (.leaf (2)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (7))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (2))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (8)) (.leaf (4))) (.branch 31 (.leaf (6)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (0))) (.branch 39 (.leaf (3)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (4)) (.leaf (2))) (.branch 43 (.leaf (6)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (8)) (.leaf (5))) (.branch 47 (.leaf (1)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (7))) (.branch 51 (.leaf (2)) (.leaf (4)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (6))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (5)) (.leaf (2))) (.branch 59 (.leaf (1)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (8)) (.leaf (4))) (.branch 63 (.leaf (7)) (.leaf (3))))))))
  code := certificateP9_5101
  counts := ![(.branch 28 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 27 (.leaf (-24)) (.leaf (-25)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-20)) (.leaf (-22)))),
  (.branch 5 (.leaf (0)) (.branch 43 (.leaf (-39)) (.leaf (-41)))),
  (.branch 11 (.leaf (0)) (.leaf (-9))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 61 (.branch 55 (.leaf (-14)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.branch 60 (.leaf (-25)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.leaf (-1)) (.leaf (0))),
  (.branch 63 (.leaf (-6)) (.leaf (-3))),
  (.branch 60 (.branch 58 (.branch 47 (.leaf (-22)) (.leaf (-21))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 59 (.branch 57 (.branch 44 (.leaf (-41)) (.leaf (-40))) (.branch 58 (.leaf (-35)) (.leaf (-30)))) (.branch 61 (.branch 60 (.leaf (-25)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 25 (.branch 12 (.leaf (-9)) (.leaf (-8))) (.branch 38 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5))))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_293_5102 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (7)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (4)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (6)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (3)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (4)) (.leaf (5)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (2))) (.branch 47 (.leaf (1)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (8)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (3)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (4)) (.leaf (5)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (2))) (.branch 63 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_5102
  counts := ![(.branch 29 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 63 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-28))),
  (.branch 20 (.leaf (0)) (.leaf (-44))),
  (.branch 52 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.leaf (-8)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 56 (.leaf (-1)) (.leaf (0))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 50 (.branch 43 (.branch 39 (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26)))) (.branch 41 (.branch 40 (.leaf (-25)) (.leaf (-24))) (.branch 42 (.leaf (-23)) (.leaf (-22))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19)))) (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.branch 31 (.branch 25 (.branch 22 (.branch 21 (.leaf (-44)) (.leaf (-43))) (.branch 23 (.leaf (-42)) (.branch 24 (.leaf (-41)) (.leaf (-40))))) (.branch 28 (.branch 26 (.leaf (-39)) (.branch 27 (.leaf (-38)) (.leaf (-37)))) (.branch 29 (.leaf (-36)) (.branch 30 (.leaf (-35)) (.leaf (-34)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-33)) (.leaf (-32))) (.branch 34 (.leaf (-31)) (.branch 35 (.leaf (-30)) (.leaf (-29))))) (.branch 39 (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26)))) (.branch 40 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-23))))))) (.branch 53 (.branch 47 (.branch 44 (.branch 43 (.leaf (-22)) (.leaf (-21))) (.branch 45 (.leaf (-20)) (.branch 46 (.leaf (-19)) (.leaf (-18))))) (.branch 50 (.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_293_5103 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (4)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (4)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (8)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (4)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (0))) (.branch 43 (.leaf (5)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (4)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (6)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (4)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (0))) (.branch 59 (.leaf (5)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (4)) (.leaf (3))))))))
  code := certificateP9_5103
  counts := ![(.branch 30 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 38 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 28 (.leaf (-19)) (.leaf (-20)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 20 (.leaf (0)) (.leaf (-12))),
  (.branch 4 (.leaf (0)) (.leaf (-60))),
  (.branch 36 (.leaf (0)) (.leaf (-28)))]
  high := ![(.branch 54 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 62 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 45 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 19 (.branch 11 (.branch 7 (.branch 5 (.leaf (-60)) (.branch 6 (.leaf (-59)) (.leaf (-58)))) (.branch 9 (.branch 8 (.leaf (-57)) (.leaf (-56))) (.branch 10 (.leaf (-55)) (.leaf (-54))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-53)) (.leaf (-52))) (.branch 14 (.leaf (-51)) (.leaf (-50)))) (.branch 17 (.branch 16 (.leaf (-49)) (.leaf (-48))) (.branch 18 (.leaf (-47)) (.leaf (-46)))))) (.branch 26 (.branch 22 (.branch 20 (.leaf (-45)) (.branch 21 (.leaf (-44)) (.leaf (-43)))) (.branch 24 (.branch 23 (.leaf (-42)) (.leaf (-41))) (.branch 25 (.leaf (-40)) (.leaf (-39))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-38)) (.leaf (-37))) (.branch 29 (.leaf (-36)) (.leaf (-35)))) (.branch 32 (.branch 31 (.leaf (-34)) (.leaf (-33))) (.branch 33 (.leaf (-32)) (.leaf (-31))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.leaf (-30)) (.branch 36 (.leaf (-29)) (.leaf (-28)))) (.branch 39 (.branch 38 (.leaf (-27)) (.leaf (-26))) (.branch 40 (.leaf (-25)) (.leaf (-24))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 44 (.leaf (-21)) (.leaf (-20)))) (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))))) (.branch 56 (.branch 52 (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 50 (.branch 43 (.branch 39 (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26)))) (.branch 41 (.branch 40 (.leaf (-25)) (.leaf (-24))) (.branch 42 (.leaf (-23)) (.leaf (-22))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19)))) (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_293_5104 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (3)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (8)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (3)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (7)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (0))) (.branch 39 (.leaf (1)) (.leaf (3))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (0))) (.branch 43 (.leaf (6)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (2))) (.branch 47 (.leaf (3)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (8)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (3))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (4)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (2))) (.branch 63 (.leaf (3)) (.leaf (6))))))))
  code := certificateP9_5104
  counts := ![(.branch 29 (.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 38 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 43 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 32 (.branch 11 (.leaf (0)) (.leaf (-31))) (.branch 53 (.leaf (-32)) (.leaf (-33)))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-28))),
  (.branch 20 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 52 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-1)),
  (.branch 60 (.branch 38 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-33)) (.leaf (-30))) (.branch 56 (.leaf (-27)) (.branch 57 (.leaf (-24)) (.leaf (-21))))) (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 22 (.leaf (-1)) (.leaf (0))),
  (.branch 50 (.branch 43 (.branch 39 (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26)))) (.branch 41 (.branch 40 (.leaf (-25)) (.leaf (-24))) (.branch 42 (.leaf (-23)) (.leaf (-22))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19)))) (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_293_5105 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (5))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (8)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (5)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (7)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (8)) (.leaf (3))) (.branch 31 (.leaf (1)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (7)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (6))) (.branch 39 (.leaf (0)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (3)) (.leaf (2))) (.branch 43 (.leaf (0)) (.leaf (8)))) (.branch 46 (.branch 45 (.leaf (5)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (6)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (7)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (5)) (.leaf (4))) (.branch 59 (.leaf (0)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (8)) (.leaf (3))) (.branch 63 (.leaf (1)) (.leaf (6))))))))
  code := certificateP9_5105
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 13 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 27 (.branch 1 (.leaf (0)) (.branch 11 (.leaf (-9)) (.leaf (-11)))) (.branch 43 (.leaf (-12)) (.branch 59 (.leaf (-13)) (.leaf (-14))))),
  (.branch 18 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 34 (.leaf (-6)) (.branch 50 (.leaf (-8)) (.leaf (-10))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 47 (.leaf (-9)) (.leaf (-10)))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-17)) (.leaf (-18)))),
  (.branch 6 (.leaf (0)) (.branch 57 (.leaf (-34)) (.leaf (-35)))),
  (.branch 25 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 61 (.branch 60 (.leaf (-14)) (.leaf (-12))) (.branch 62 (.leaf (-10)) (.branch 63 (.leaf (-8)) (.leaf (-6))))),
  (.branch 57 (.leaf (-10)) (.leaf (-9))),
  (.branch 62 (.branch 61 (.leaf (-10)) (.leaf (-8))) (.branch 63 (.leaf (-6)) (.leaf (-4)))),
  (.branch 63 (.leaf (-6)) (.leaf (-3))),
  (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 60 (.branch 58 (.leaf (-35)) (.branch 59 (.leaf (-30)) (.leaf (-25)))) (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 39 (.branch 26 (.leaf (-3)) (.leaf (-2))) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.branch 58 (.branch 55 (.branch 37 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 62 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_293_5106 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (6)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (7)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (3)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (8)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (1))) (.branch 47 (.leaf (0)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (4)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (5)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (1))) (.branch 63 (.leaf (0)) (.leaf (2))))))))
  code := certificateP9_5106
  counts := ![(.branch 31 (.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))) (.branch 47 (.branch 39 (.branch 33 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14)))) (.branch 41 (.leaf (15)) (.branch 44 (.leaf (16)) (.leaf (17))))) (.branch 55 (.branch 49 (.leaf (18)) (.branch 52 (.leaf (19)) (.leaf (20)))) (.branch 60 (.branch 57 (.leaf (21)) (.leaf (22))) (.branch 63 (.leaf (23)) (.leaf (24))))))),
  (.branch 30 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 32 (.branch 16 (.branch 8 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 48 (.branch 40 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 45 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 53 (.leaf (12)) (.leaf (13))) (.branch 61 (.leaf (14)) (.branch 64 (.leaf (15)) (.leaf (16))))))),
  (.branch 3 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2)))),
  (.branch 59 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-29))),
  (.branch 19 (.leaf (0)) (.leaf (-13))),
  (.branch 59 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-53))),
  (.branch 27 (.leaf (0)) (.leaf (-37))),
  (.branch 43 (.leaf (0)) (.leaf (-21)))]
  high := ![(.branch 58 (.leaf (-5)) (.branch 61 (.leaf (-4)) (.leaf (-3)))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 49 (.branch 42 (.branch 38 (.branch 36 (.leaf (-29)) (.branch 37 (.leaf (-28)) (.leaf (-27)))) (.branch 40 (.branch 39 (.leaf (-26)) (.leaf (-25))) (.branch 41 (.leaf (-24)) (.leaf (-23))))) (.branch 45 (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20)))) (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))))) (.branch 56 (.branch 52 (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 37 (.branch 24 (.branch 17 (.branch 14 (.branch 12 (.leaf (-53)) (.branch 13 (.leaf (-52)) (.leaf (-51)))) (.branch 15 (.leaf (-50)) (.branch 16 (.leaf (-49)) (.leaf (-48))))) (.branch 20 (.branch 18 (.leaf (-47)) (.branch 19 (.leaf (-46)) (.leaf (-45)))) (.branch 22 (.branch 21 (.leaf (-44)) (.leaf (-43))) (.branch 23 (.leaf (-42)) (.leaf (-41)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-40)) (.branch 26 (.leaf (-39)) (.leaf (-38)))) (.branch 28 (.leaf (-37)) (.branch 29 (.leaf (-36)) (.leaf (-35))))) (.branch 33 (.branch 31 (.leaf (-34)) (.branch 32 (.leaf (-33)) (.leaf (-32)))) (.branch 35 (.branch 34 (.leaf (-31)) (.leaf (-30))) (.branch 36 (.leaf (-29)) (.leaf (-28))))))) (.branch 50 (.branch 43 (.branch 40 (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19)))) (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 45 (.branch 36 (.branch 31 (.branch 29 (.branch 28 (.leaf (-37)) (.leaf (-36))) (.branch 30 (.leaf (-35)) (.leaf (-34)))) (.branch 33 (.branch 32 (.leaf (-33)) (.leaf (-32))) (.branch 34 (.leaf (-31)) (.branch 35 (.leaf (-30)) (.leaf (-29)))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 42 (.branch 41 (.leaf (-24)) (.leaf (-23))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))))) (.branch 54 (.branch 49 (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 53 (.branch 48 (.branch 45 (.branch 44 (.leaf (-21)) (.leaf (-20))) (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17))))) (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_293_5107 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (6)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (7)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (1)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (3)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (5))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (6)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (0))) (.branch 47 (.leaf (1)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (5))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (8)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (0))) (.branch 63 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_5107
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))))) (.branch 47 (.branch 38 (.branch 34 (.leaf (10)) (.leaf (11))) (.branch 41 (.leaf (12)) (.branch 44 (.leaf (13)) (.leaf (14))))) (.branch 57 (.branch 50 (.leaf (15)) (.branch 54 (.leaf (16)) (.leaf (17)))) (.branch 60 (.leaf (18)) (.branch 63 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 59 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.branch 10 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-21))),
  (.branch 27 (.leaf (0)) (.leaf (-37))),
  (.branch 59 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 59 (.leaf (-14)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 51 (.leaf (-6)) (.leaf (-5))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 48 (.branch 45 (.branch 44 (.leaf (-21)) (.leaf (-20))) (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17))))) (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 36 (.branch 31 (.branch 29 (.branch 28 (.leaf (-37)) (.leaf (-36))) (.branch 30 (.leaf (-35)) (.leaf (-34)))) (.branch 33 (.branch 32 (.leaf (-33)) (.leaf (-32))) (.branch 34 (.leaf (-31)) (.branch 35 (.leaf (-30)) (.leaf (-29)))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 42 (.branch 41 (.leaf (-24)) (.leaf (-23))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))))) (.branch 54 (.branch 49 (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_293_5108 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (6))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (4)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (4))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (7))) (.branch 27 (.leaf (3)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (4)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (3)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (4))) (.branch 39 (.leaf (1)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (8))) (.branch 43 (.leaf (3)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (2))) (.branch 47 (.leaf (4)) (.leaf (1)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (3)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (4))) (.branch 55 (.leaf (2)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (5))) (.branch 59 (.leaf (3)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_5108
  counts := ![(.branch 29 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 36 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 48 (.branch 39 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 57 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 32 (.branch 14 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))) (.branch 50 (.branch 41 (.branch 37 (.leaf (7)) (.leaf (8))) (.branch 46 (.leaf (9)) (.leaf (10)))) (.branch 60 (.branch 55 (.leaf (11)) (.leaf (12))) (.branch 64 (.leaf (13)) (.leaf (14)))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 58 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-18))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 58 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.leaf (-54))),
  (.branch 26 (.leaf (0)) (.leaf (-38))),
  (.branch 42 (.leaf (0)) (.leaf (-22)))]
  high := ![(.branch 62 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 58 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 63 (.leaf (-14)) (.leaf (-7)))),
  (.branch 51 (.leaf (-2)) (.leaf (0))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 37 (.branch 23 (.branch 16 (.branch 13 (.branch 11 (.leaf (-54)) (.branch 12 (.leaf (-53)) (.leaf (-52)))) (.branch 14 (.leaf (-51)) (.branch 15 (.leaf (-50)) (.leaf (-49))))) (.branch 19 (.branch 17 (.leaf (-48)) (.branch 18 (.leaf (-47)) (.leaf (-46)))) (.branch 21 (.branch 20 (.leaf (-45)) (.leaf (-44))) (.branch 22 (.leaf (-43)) (.leaf (-42)))))) (.branch 30 (.branch 26 (.branch 24 (.leaf (-41)) (.branch 25 (.leaf (-40)) (.leaf (-39)))) (.branch 28 (.branch 27 (.leaf (-38)) (.leaf (-37))) (.branch 29 (.leaf (-36)) (.leaf (-35))))) (.branch 33 (.branch 31 (.leaf (-34)) (.branch 32 (.leaf (-33)) (.leaf (-32)))) (.branch 35 (.branch 34 (.leaf (-31)) (.leaf (-30))) (.branch 36 (.leaf (-29)) (.leaf (-28))))))) (.branch 50 (.branch 43 (.branch 40 (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19)))) (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 45 (.branch 35 (.branch 30 (.branch 28 (.branch 27 (.leaf (-38)) (.leaf (-37))) (.branch 29 (.leaf (-36)) (.leaf (-35)))) (.branch 32 (.branch 31 (.leaf (-34)) (.leaf (-33))) (.branch 33 (.leaf (-32)) (.branch 34 (.leaf (-31)) (.leaf (-30)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-29)) (.leaf (-28))) (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-25))))) (.branch 42 (.branch 41 (.leaf (-24)) (.leaf (-23))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))))) (.branch 54 (.branch 49 (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 53 (.branch 47 (.branch 44 (.branch 43 (.leaf (-22)) (.leaf (-21))) (.branch 45 (.leaf (-20)) (.branch 46 (.leaf (-19)) (.leaf (-18))))) (.branch 50 (.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_293_5109 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (8))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (5))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (7))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (2))) (.branch 31 (.leaf (0)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (5)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (6))) (.branch 39 (.leaf (1)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (3)) (.leaf (8))) (.branch 43 (.leaf (0)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (2))) (.branch 47 (.leaf (0)) (.leaf (5)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (6)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (3))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (4)) (.leaf (7))) (.branch 59 (.leaf (0)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (5)) (.leaf (2))) (.branch 63 (.leaf (0)) (.leaf (6))))))))
  code := certificateP9_5109
  counts := ![(.branch 31 (.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 47 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 40 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 56 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 63 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 61 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 13 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.leaf (0)) (.branch 58 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 20 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-8)) (.leaf (-9)))) (.branch 36 (.branch 33 (.leaf (-10)) (.leaf (-11))) (.branch 49 (.leaf (-12)) (.branch 52 (.leaf (-13)) (.leaf (-14)))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 41 (.leaf (-49)) (.leaf (-51)))),
  (.branch 6 (.leaf (0)) (.branch 57 (.leaf (-34)) (.leaf (-35)))),
  (.branch 9 (.leaf (0)) (.leaf (-19))),
  (.branch 25 (.leaf (0)) (.leaf (-3))),
  (.branch 26 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.leaf (-22)))]
  high := ![(.branch 53 (.leaf (-14)) (.branch 60 (.leaf (-13)) (.leaf (-11)))),
  (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 54 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 58 (.branch 55 (.branch 42 (.leaf (-51)) (.leaf (-50))) (.branch 56 (.leaf (-45)) (.branch 57 (.leaf (-40)) (.leaf (-35))))) (.branch 61 (.branch 59 (.leaf (-30)) (.branch 60 (.leaf (-25)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 60 (.branch 58 (.leaf (-35)) (.branch 59 (.leaf (-30)) (.leaf (-25)))) (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 36 (.branch 10 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17)))) (.branch 62 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 39 (.branch 26 (.leaf (-3)) (.leaf (-2))) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 47 (.branch 44 (.branch 43 (.leaf (-22)) (.leaf (-21))) (.branch 45 (.leaf (-20)) (.branch 46 (.leaf (-19)) (.leaf (-18))))) (.branch 50 (.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_293_5110 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (7)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (6)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (8)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (5))) (.branch 23 (.leaf (3)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (7)) (.leaf (2))) (.branch 31 (.leaf (6)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (3)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (4))) (.branch 39 (.leaf (8)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (5))) (.branch 43 (.leaf (2)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (3)) (.leaf (1))) (.branch 47 (.leaf (6)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (7)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (5))) (.branch 55 (.leaf (3)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (4))) (.branch 59 (.leaf (1)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (8)) (.leaf (2))) (.branch 63 (.leaf (6)) (.leaf (5))))))))
  code := certificateP9_5110
  counts := ![(.branch 28 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 37 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 14 (.leaf (-24)) (.leaf (-26)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 30 (.leaf (-9)) (.leaf (-10)))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 23 (.leaf (-9)) (.branch 55 (.leaf (-10)) (.leaf (-11))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (-5))) (.branch 26 (.leaf (-6)) (.branch 58 (.leaf (-7)) (.leaf (-8))))),
  (.branch 10 (.leaf (0)) (.branch 42 (.leaf (-1)) (.leaf (-2)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-29))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (-5)) (.leaf (-8))))]
  high := ![(.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 61 (.branch 47 (.leaf (-26)) (.branch 60 (.leaf (-25)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 63 (.leaf (-10)) (.leaf (-5))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8)))) (.branch 61 (.branch 60 (.leaf (-7)) (.leaf (-6))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 61 (.branch 59 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 43 (.leaf (-2)) (.branch 55 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 56 (.branch 52 (.branch 8 (.leaf (-29)) (.branch 30 (.leaf (-28)) (.leaf (-27)))) (.branch 54 (.branch 53 (.leaf (-25)) (.leaf (-23))) (.branch 55 (.leaf (-21)) (.leaf (-19))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-17)) (.leaf (-15))) (.branch 59 (.leaf (-13)) (.leaf (-11)))) (.branch 62 (.branch 61 (.leaf (-9)) (.leaf (-7))) (.branch 63 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 62 (.branch 40 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-5)) (.leaf (-3))))]
def witnessP9_293_5111 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (6))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (7))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (3)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (6))) (.branch 39 (.leaf (1)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (4)) (.leaf (2))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (5)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (8))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (4)) (.leaf (2))) (.branch 59 (.leaf (0)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_5111
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 40 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 56 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 37 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-26))),
  (.branch 22 (.leaf (0)) (.leaf (-42))),
  (.branch 54 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 53 (.leaf (-12)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 61 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 51 (.branch 44 (.branch 41 (.branch 39 (.leaf (-26)) (.branch 40 (.leaf (-25)) (.leaf (-24)))) (.branch 42 (.leaf (-23)) (.branch 43 (.leaf (-22)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-20)) (.branch 46 (.leaf (-19)) (.leaf (-18)))) (.branch 49 (.branch 48 (.leaf (-17)) (.leaf (-16))) (.branch 50 (.leaf (-15)) (.leaf (-14)))))) (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 32 (.branch 27 (.branch 24 (.branch 23 (.leaf (-42)) (.leaf (-41))) (.branch 25 (.leaf (-40)) (.branch 26 (.leaf (-39)) (.leaf (-38))))) (.branch 29 (.branch 28 (.leaf (-37)) (.leaf (-36))) (.branch 30 (.leaf (-35)) (.branch 31 (.leaf (-34)) (.leaf (-33)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (-32)) (.leaf (-31))) (.branch 35 (.leaf (-30)) (.branch 36 (.leaf (-29)) (.leaf (-28))))) (.branch 40 (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22))))))) (.branch 53 (.branch 48 (.branch 45 (.branch 44 (.leaf (-21)) (.leaf (-20))) (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17))))) (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_293_5112 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (6)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (7)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (3)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (6)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (5)) (.leaf (1))) (.branch 47 (.leaf (0)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (8)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (5)) (.leaf (1))) (.branch 63 (.leaf (0)) (.leaf (2))))))))
  code := certificateP9_5112
  counts := ![(.branch 31 (.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))) (.branch 47 (.branch 39 (.branch 33 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14)))) (.branch 41 (.leaf (15)) (.branch 44 (.leaf (16)) (.leaf (17))))) (.branch 55 (.branch 49 (.leaf (18)) (.branch 52 (.leaf (19)) (.leaf (20)))) (.branch 60 (.branch 57 (.leaf (21)) (.leaf (22))) (.branch 63 (.leaf (23)) (.leaf (24))))))),
  (.branch 30 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 32 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 59 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-21))),
  (.branch 27 (.leaf (0)) (.leaf (-37))),
  (.branch 59 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 58 (.leaf (-5)) (.branch 61 (.leaf (-4)) (.leaf (-3)))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 53 (.branch 48 (.branch 45 (.branch 44 (.leaf (-21)) (.leaf (-20))) (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17))))) (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 36 (.branch 31 (.branch 29 (.branch 28 (.leaf (-37)) (.leaf (-36))) (.branch 30 (.leaf (-35)) (.leaf (-34)))) (.branch 33 (.branch 32 (.leaf (-33)) (.leaf (-32))) (.branch 34 (.leaf (-31)) (.branch 35 (.leaf (-30)) (.leaf (-29)))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 42 (.branch 41 (.leaf (-24)) (.leaf (-23))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))))) (.branch 54 (.branch 49 (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_293_5113 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (7)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (6))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (3))) (.branch 15 (.leaf (8)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (3))) (.branch 23 (.leaf (7)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (6)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (4)) (.leaf (8))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (3))) (.branch 35 (.leaf (1)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (5)) (.leaf (7))) (.branch 39 (.leaf (2)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (6))) (.branch 43 (.leaf (4)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (3))) (.branch 47 (.leaf (8)) (.leaf (1)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (5)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (7))) (.branch 55 (.leaf (3)) (.leaf (4))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (6)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (1))) (.branch 63 (.leaf (8)) (.leaf (5))))))))
  code := certificateP9_5113
  counts := ![(.branch 28 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 48 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 13 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 48 (.leaf (-14)) (.branch 62 (.leaf (-17)) (.leaf (-18))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.leaf (-11))) (.branch 39 (.leaf (-13)) (.leaf (-16)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 22 (.leaf (-18)) (.branch 55 (.leaf (-25)) (.leaf (-28))))),
  (.branch 5 (.leaf (0)) (.branch 43 (.leaf (-39)) (.leaf (-41)))),
  (.branch 24 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.branch 38 (.leaf (-9)) (.leaf (-10)))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 63 (.leaf (-18)) (.leaf (-14))),
  (.branch 51 (.branch 40 (.leaf (-16)) (.leaf (-15))) (.branch 62 (.leaf (-14)) (.branch 63 (.leaf (-10)) (.leaf (-6))))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-28)) (.leaf (-26))) (.branch 58 (.leaf (-24)) (.leaf (-22)))) (.branch 61 (.branch 60 (.leaf (-20)) (.leaf (-18))) (.branch 62 (.leaf (-16)) (.branch 63 (.leaf (-14)) (.leaf (-12)))))),
  (.branch 59 (.branch 57 (.branch 44 (.leaf (-41)) (.leaf (-40))) (.branch 58 (.leaf (-35)) (.leaf (-30)))) (.branch 61 (.branch 60 (.leaf (-25)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 38 (.leaf (-2)) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.branch 61 (.branch 43 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_293_5114 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (8)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (3)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (7)) (.leaf (6))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (8)) (.leaf (4))) (.branch 59 (.leaf (0)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_5114
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 57 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-17)) (.leaf (-18)))),
  (.branch 10 (.leaf (0)) (.leaf (-34))),
  (.branch 21 (.leaf (0)) (.branch 42 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-23))),
  (.branch 25 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 56 (.leaf (-13)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 61 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 58 (.branch 55 (.branch 11 (.leaf (-34)) (.branch 54 (.leaf (-33)) (.leaf (-30)))) (.branch 56 (.leaf (-27)) (.branch 57 (.leaf (-24)) (.leaf (-21))))) (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 43 (.leaf (-2)) (.leaf (0))),
  (.branch 52 (.branch 46 (.branch 43 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))))) (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_293_5115 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (1)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (7)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 31 (.leaf (1)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (3)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (5)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (4)) (.leaf (0))) (.branch 43 (.leaf (1)) (.leaf (6)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (3))) (.branch 47 (.leaf (1)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (4)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (0))) (.branch 59 (.leaf (1)) (.leaf (8)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (4))) (.branch 63 (.leaf (1)) (.leaf (2))))))))
  code := certificateP9_5115
  counts := ![(.branch 29 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 45 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 61 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 59 (.leaf (14)) (.branch 63 (.leaf (15)) (.leaf (16))))))),
  (.branch 32 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 60 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (-5)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-20))),
  (.branch 28 (.leaf (0)) (.leaf (-36))),
  (.branch 60 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 59 (.branch 47 (.branch 36 (.leaf (-23)) (.leaf (-22))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 52 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.branch 49 (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16))))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 37 (.branch 32 (.branch 30 (.branch 29 (.leaf (-36)) (.leaf (-35))) (.branch 31 (.leaf (-34)) (.leaf (-33)))) (.branch 34 (.branch 33 (.leaf (-32)) (.leaf (-31))) (.branch 35 (.leaf (-30)) (.branch 36 (.leaf (-29)) (.leaf (-28)))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-27)) (.leaf (-26))) (.branch 40 (.leaf (-25)) (.leaf (-24)))) (.branch 43 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))))) (.branch 55 (.branch 50 (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 52 (.branch 51 (.leaf (-14)) (.leaf (-13))) (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_293_5116 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (8)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (6)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (7)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (3)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (8)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (6))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (4)) (.leaf (2)))) (.branch 46 (.branch 45 (.leaf (3)) (.leaf (0))) (.branch 47 (.leaf (1)) (.leaf (7)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (5)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (3))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (8)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (6)) (.leaf (0))) (.branch 63 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_5116
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 38 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.branch 10 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.leaf (-22))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-2))) (.branch 18 (.leaf (-4)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-23)) (.leaf (-25)))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (-40)) (.leaf (-41)))),
  (.branch 40 (.branch 19 (.leaf (0)) (.leaf (-7))) (.branch 61 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.leaf (-49))),
  (.branch 16 (.leaf (0)) (.branch 37 (.leaf (-16)) (.leaf (-17))))]
  high := ![(.branch 59 (.leaf (-14)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 61 (.branch 35 (.leaf (-22)) (.branch 48 (.leaf (-21)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 51 (.leaf (-6)) (.leaf (-5))),
  (.branch 59 (.branch 57 (.branch 46 (.leaf (-25)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 54 (.leaf (-1)) (.leaf (0))),
  (.branch 57 (.branch 53 (.branch 30 (.leaf (-41)) (.branch 52 (.leaf (-39)) (.leaf (-36)))) (.branch 55 (.branch 54 (.leaf (-33)) (.leaf (-30))) (.branch 56 (.leaf (-27)) (.leaf (-24))))) (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 55 (.branch 51 (.branch 49 (.branch 6 (.leaf (-49)) (.leaf (-48))) (.branch 50 (.leaf (-45)) (.leaf (-42)))) (.branch 53 (.branch 52 (.leaf (-39)) (.leaf (-36))) (.branch 54 (.leaf (-33)) (.leaf (-30))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-27)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 61 (.branch 38 (.leaf (-17)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_293_5117 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (7)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (3)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (6))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (3)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (0))) (.branch 43 (.leaf (1)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (0))) (.branch 47 (.leaf (1)) (.leaf (8)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (3)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (4)) (.leaf (5))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_5117
  counts := ![(.branch 30 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 29 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 38 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 43 (.leaf (9)) (.leaf (10)))) (.branch 57 (.branch 52 (.leaf (11)) (.leaf (12))) (.branch 61 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))) (.branch 50 (.branch 41 (.branch 36 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 59 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.leaf (0)) (.branch 64 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-18))) (.branch 15 (.leaf (-22)) (.leaf (-23)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 22 (.leaf (-5)) (.branch 31 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 16 (.leaf (0)) (.leaf (-48))),
  (.branch 48 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 54 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 62 (.branch 48 (.leaf (-23)) (.leaf (-21))) (.branch 63 (.leaf (-14)) (.leaf (-7)))),
  (.leaf (-7)),
  (.branch 61 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 40 (.branch 28 (.branch 22 (.branch 19 (.branch 17 (.leaf (-48)) (.branch 18 (.leaf (-47)) (.leaf (-46)))) (.branch 20 (.leaf (-45)) (.branch 21 (.leaf (-44)) (.leaf (-43))))) (.branch 25 (.branch 23 (.leaf (-42)) (.branch 24 (.leaf (-41)) (.leaf (-40)))) (.branch 26 (.leaf (-39)) (.branch 27 (.leaf (-38)) (.leaf (-37)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-36)) (.branch 30 (.leaf (-35)) (.leaf (-34)))) (.branch 32 (.leaf (-33)) (.branch 33 (.leaf (-32)) (.leaf (-31))))) (.branch 37 (.branch 35 (.leaf (-30)) (.branch 36 (.leaf (-29)) (.leaf (-28)))) (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-25))))))) (.branch 52 (.branch 46 (.branch 43 (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22)))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))))) (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.leaf (-13)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_293_5118 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (7)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (6))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (4))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (3))) (.branch 31 (.leaf (8)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (4)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (6))) (.branch 39 (.leaf (3)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (5)) (.leaf (0))) (.branch 43 (.leaf (2)) (.leaf (4)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (7)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (6))) (.branch 55 (.leaf (0)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (5)) (.leaf (3))) (.branch 59 (.leaf (2)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (4))) (.branch 63 (.leaf (8)) (.leaf (2))))))))
  code := certificateP9_5118
  counts := ![(.branch 28 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 55 (.branch 51 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 16 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.leaf (7))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))),
  (.branch 31 (.leaf (0)) (.branch 63 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 14 (.leaf (-29)) (.branch 23 (.leaf (-30)) (.leaf (-31))))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 36 (.leaf (-4)) (.branch 52 (.leaf (-6)) (.leaf (-8))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-43)) (.leaf (-44)))) (.branch 30 (.leaf (-45)) (.branch 39 (.leaf (-46)) (.leaf (-47))))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-17))),
  (.branch 31 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 61 (.branch 56 (.leaf (-31)) (.leaf (-28))) (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 62 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 53 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 60 (.branch 40 (.leaf (-47)) (.branch 59 (.leaf (-42)) (.leaf (-35)))) (.branch 62 (.branch 61 (.leaf (-28)) (.leaf (-21))) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 8 (.leaf (-15)) (.branch 63 (.leaf (-14)) (.leaf (-7)))),
  (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 55 (.branch 51 (.branch 49 (.branch 48 (.leaf (-17)) (.leaf (-16))) (.branch 50 (.leaf (-15)) (.leaf (-14)))) (.branch 53 (.branch 52 (.leaf (-13)) (.leaf (-12))) (.branch 54 (.leaf (-11)) (.leaf (-10))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_293_5119 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (8)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (7)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (6))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (1))) (.branch 23 (.leaf (8)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (4))) (.branch 27 (.leaf (2)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (6)) (.leaf (7))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (4)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (5))) (.branch 39 (.leaf (8)) (.leaf (3))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (2)) (.leaf (6)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (0))) (.branch 47 (.leaf (1)) (.leaf (7)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (3)) (.leaf (5))) (.branch 51 (.leaf (0)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (1))) (.branch 55 (.leaf (8)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (6)) (.leaf (3))) (.branch 59 (.leaf (2)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (7))))))))
  code := certificateP9_5119
  counts := ![(.branch 29 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 56 (.branch 51 (.leaf (11)) (.leaf (12))) (.branch 61 (.leaf (13)) (.leaf (14)))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.leaf (7))))),
  (.branch 38 (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-11)) (.leaf (-13)))) (.branch 37 (.leaf (-14)) (.branch 46 (.leaf (-15)) (.leaf (-16))))),
  (.branch 2 (.leaf (0)) (.leaf (-22))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (-31))) (.branch 30 (.leaf (-33)) (.leaf (-34)))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-6)) (.leaf (-7)))) (.branch 53 (.branch 35 (.leaf (-8)) (.leaf (-9))) (.branch 62 (.leaf (-11)) (.leaf (-12))))),
  (.branch 12 (.leaf (0)) (.branch 50 (.leaf (-4)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-34)) (.leaf (-38)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 57 (.branch 47 (.leaf (-16)) (.branch 52 (.leaf (-15)) (.leaf (-14)))) (.branch 62 (.leaf (-13)) (.branch 63 (.leaf (-10)) (.leaf (-7))))),
  (.branch 61 (.branch 35 (.leaf (-22)) (.branch 48 (.leaf (-21)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 31 (.leaf (-34)) (.branch 59 (.leaf (-32)) (.leaf (-27)))) (.branch 62 (.branch 61 (.leaf (-22)) (.leaf (-17))) (.branch 63 (.leaf (-12)) (.leaf (-7))))),
  (.branch 63 (.leaf (-12)) (.leaf (-7))),
  (.branch 51 (.leaf (-6)) (.leaf (-5))),
  (.branch 59 (.branch 32 (.branch 19 (.leaf (-38)) (.leaf (-37))) (.branch 45 (.leaf (-36)) (.branch 58 (.leaf (-35)) (.leaf (-30))))) (.branch 61 (.branch 60 (.leaf (-25)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))))),
  (.leaf (0)),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_293_5120 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (8))) (.branch 15 (.leaf (0)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (3))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (4))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (7))) (.branch 31 (.leaf (3)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (4)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (0))) (.branch 39 (.leaf (1)) (.leaf (3))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (5)) (.leaf (0))) (.branch 43 (.leaf (2)) (.leaf (4)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (8))) (.branch 47 (.leaf (0)) (.leaf (6)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (4))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (6)) (.leaf (3))) (.branch 59 (.leaf (2)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (7))) (.branch 63 (.leaf (4)) (.leaf (5))))))))
  code := certificateP9_5120
  counts := ![(.branch 28 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 56 (.branch 51 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.leaf (0)) (.branch 62 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 19 (.leaf (-26)) (.branch 28 (.leaf (-27)) (.leaf (-28))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-43)) (.leaf (-44)))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-8)) (.leaf (-9)))) (.branch 35 (.leaf (-10)) (.branch 44 (.leaf (-11)) (.leaf (-12))))),
  (.branch 9 (.leaf (0)) (.branch 41 (.leaf (-2)) (.leaf (-3)))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (-6))) (.branch 57 (.leaf (-8)) (.leaf (-9)))),
  (.branch 30 (.leaf (0)) (.leaf (-2))),
  (.branch 14 (.leaf (0)) (.leaf (-18)))]
  high := ![(.branch 62 (.branch 61 (.leaf (-28)) (.leaf (-21))) (.branch 63 (.leaf (-14)) (.leaf (-7)))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 13 (.leaf (-44)) (.branch 59 (.leaf (-42)) (.leaf (-35)))) (.branch 62 (.branch 61 (.leaf (-28)) (.leaf (-21))) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 45 (.leaf (-12)) (.leaf (-7))),
  (.branch 54 (.branch 42 (.leaf (-3)) (.leaf (-2))) (.branch 55 (.leaf (-1)) (.leaf (0)))),
  (.branch 60 (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7)))) (.branch 62 (.branch 61 (.leaf (-6)) (.leaf (-5))) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 55 (.branch 50 (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 52 (.branch 51 (.leaf (-14)) (.leaf (-13))) (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_293_5121 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (6))) (.branch 15 (.leaf (0)) (.leaf (7)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (3))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (8)) (.leaf (4))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (6))) (.branch 31 (.leaf (3)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (4)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (0))) (.branch 39 (.leaf (1)) (.leaf (3))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (5)) (.leaf (0))) (.branch 43 (.leaf (2)) (.leaf (4)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (6))) (.branch 47 (.leaf (0)) (.leaf (8)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (4))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (7)) (.leaf (3))) (.branch 59 (.leaf (2)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (6))) (.branch 63 (.leaf (4)) (.leaf (5))))))))
  code := certificateP9_5121
  counts := ![(.branch 28 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 56 (.branch 51 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 19 (.leaf (-26)) (.branch 28 (.leaf (-27)) (.leaf (-28))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-43)) (.leaf (-44)))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-8)) (.leaf (-9)))) (.branch 35 (.leaf (-10)) (.branch 44 (.leaf (-11)) (.leaf (-12))))),
  (.branch 9 (.leaf (0)) (.branch 41 (.leaf (-2)) (.leaf (-3)))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (-6))) (.branch 57 (.leaf (-7)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (-17)) (.leaf (-19))))]
  high := ![(.branch 62 (.branch 61 (.leaf (-28)) (.leaf (-21))) (.branch 63 (.leaf (-14)) (.leaf (-7)))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 13 (.leaf (-44)) (.branch 59 (.leaf (-42)) (.leaf (-35)))) (.branch 62 (.branch 61 (.leaf (-28)) (.leaf (-21))) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 45 (.leaf (-12)) (.leaf (-7))),
  (.branch 54 (.branch 42 (.leaf (-3)) (.leaf (-2))) (.branch 55 (.leaf (-1)) (.leaf (0)))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 60 (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7)))) (.branch 62 (.branch 61 (.leaf (-6)) (.leaf (-5))) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 55 (.branch 51 (.branch 49 (.branch 26 (.leaf (-19)) (.leaf (-18))) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 53 (.branch 52 (.leaf (-15)) (.leaf (-14))) (.branch 54 (.leaf (-13)) (.leaf (-12))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8)))) (.branch 61 (.branch 60 (.leaf (-7)) (.leaf (-6))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3)))))))]
def witnessP9_293_5122 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (6))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (7)) (.leaf (3))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (2))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (6))) (.branch 31 (.leaf (3)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (4)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (8)) (.leaf (0))) (.branch 39 (.leaf (1)) (.leaf (3))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (5)) (.leaf (2))) (.branch 43 (.leaf (0)) (.leaf (4)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (6))) (.branch 47 (.leaf (0)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (7)) (.leaf (4))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (5)) (.leaf (2))) (.branch 59 (.leaf (3)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (6))) (.branch 63 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_5122
  counts := ![(.branch 28 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 43 (.leaf (9)) (.leaf (10)))) (.branch 56 (.branch 51 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.leaf (7))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.leaf (0)) (.branch 53 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 28 (.branch 1 (.leaf (0)) (.branch 19 (.leaf (-11)) (.leaf (-13)))) (.branch 51 (.leaf (-14)) (.branch 60 (.leaf (-15)) (.leaf (-16))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 36 (.leaf (-4)) (.branch 52 (.leaf (-5)) (.leaf (-6))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-31)) (.leaf (-32)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (-6))) (.branch 35 (.leaf (-7)) (.branch 44 (.leaf (-9)) (.leaf (-10))))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 21 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.leaf (-27)))]
  high := ![(.branch 62 (.branch 61 (.leaf (-16)) (.leaf (-13))) (.branch 63 (.leaf (-10)) (.leaf (-7)))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 59 (.branch 53 (.leaf (-6)) (.leaf (-5))) (.branch 60 (.leaf (-3)) (.branch 61 (.leaf (-1)) (.leaf (0))))),
  (.branch 60 (.branch 13 (.leaf (-32)) (.branch 50 (.leaf (-31)) (.leaf (-27)))) (.branch 62 (.branch 61 (.leaf (-22)) (.leaf (-17))) (.branch 63 (.leaf (-12)) (.leaf (-7))))),
  (.branch 45 (.leaf (-10)) (.leaf (-7))),
  (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.branch 43 (.branch 40 (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19)))) (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_293 : Fin 46 → CycleWitness 9 := ![witnessP9_293_5077, witnessP9_293_5078, witnessP9_293_5079, witnessP9_293_5080, witnessP9_293_5081, witnessP9_293_5082, witnessP9_293_5083, witnessP9_293_5084, witnessP9_293_5085, witnessP9_293_5086, witnessP9_293_5087, witnessP9_293_5088, witnessP9_293_5089, witnessP9_293_5090, witnessP9_293_5091, witnessP9_293_5092, witnessP9_293_5093, witnessP9_293_5094, witnessP9_293_5095, witnessP9_293_5096, witnessP9_293_5097, witnessP9_293_5098, witnessP9_293_5099, witnessP9_293_5100, witnessP9_293_5101, witnessP9_293_5102, witnessP9_293_5103, witnessP9_293_5104, witnessP9_293_5105, witnessP9_293_5106, witnessP9_293_5107, witnessP9_293_5108, witnessP9_293_5109, witnessP9_293_5110, witnessP9_293_5111, witnessP9_293_5112, witnessP9_293_5113, witnessP9_293_5114, witnessP9_293_5115, witnessP9_293_5116, witnessP9_293_5117, witnessP9_293_5118, witnessP9_293_5119, witnessP9_293_5120, witnessP9_293_5121, witnessP9_293_5122]
end RealPinwheel.FiveSixths


