-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_299
-- name    : RealPinwheel_FiveSixths_WitnessP9_299
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:26:04.060384+00:00
-- url     : https://prove2.me/theorems/5bed64a3-d4b2-4bb3-9d95-026d836a200f
-- title:
--   Exact witness block P9_299
-- statement:
--   These exact witnesses represent words 5366 through 5415 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 5366–5415; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_299_5365 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (1)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (7)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (0))) (.branch 36 (.leaf (1)) (.leaf (4))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (1)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (2))) (.branch 44 (.leaf (1)) (.leaf (5)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (8)) (.leaf (0))) (.branch 51 (.leaf (1)) (.leaf (4))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (1)) (.leaf (5))))))))
  code := certificateP9_5365
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 29 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-26))),
  (.branch 19 (.leaf (0)) (.leaf (-41))),
  (.branch 49 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-8)) (.leaf (-4)))),
  (.branch 52 (.branch 48 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.leaf (-4)))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (-41)) (.leaf (-40))) (.branch 22 (.leaf (-39)) (.branch 23 (.leaf (-38)) (.leaf (-37))))) (.branch 26 (.branch 25 (.leaf (-36)) (.leaf (-35))) (.branch 27 (.leaf (-34)) (.branch 28 (.leaf (-33)) (.leaf (-32)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-31)) (.leaf (-30))) (.branch 32 (.leaf (-29)) (.branch 33 (.leaf (-28)) (.leaf (-27))))) (.branch 36 (.branch 35 (.leaf (-26)) (.leaf (-25))) (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22))))))) (.branch 49 (.branch 44 (.branch 41 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17))))) (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_299_5366 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (8))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (7)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (6)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (8))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (5)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (7))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (0))) (.branch 36 (.leaf (4)) (.leaf (8))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (0))) (.branch 40 (.leaf (2)) (.leaf (5)))) (.branch 43 (.branch 42 (.leaf (3)) (.leaf (0))) (.branch 44 (.leaf (1)) (.leaf (7)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (6)) (.leaf (0))) (.branch 51 (.leaf (1)) (.leaf (8))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (5)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (4)) (.leaf (7))))))))
  code := certificateP9_5366
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 12 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-6)) (.leaf (-7)))),
  (.branch 23 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 51 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-4))))),
  (.branch 58 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_299_5367 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (0)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (5)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (8)) (.leaf (0))) (.branch 36 (.leaf (3)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 40 (.leaf (0)) (.leaf (6)))) (.branch 43 (.branch 42 (.leaf (3)) (.leaf (1))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (3))) (.branch 55 (.leaf (0)) (.leaf (5)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (3))))))))
  code := certificateP9_5367
  counts := ![(.branch 29 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 44 (.branch 35 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 38 (.leaf (12)) (.branch 40 (.leaf (13)) (.leaf (14))))) (.branch 53 (.branch 46 (.leaf (15)) (.branch 50 (.leaf (16)) (.leaf (17)))) (.branch 55 (.leaf (18)) (.branch 59 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 33 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 36 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 56 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 19 (.leaf (0)) (.leaf (-11))),
  (.branch 26 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-19))),
  (.branch 4 (.leaf (0)) (.leaf (-56))),
  (.branch 34 (.leaf (0)) (.leaf (-26)))]
  high := ![(.branch 56 (.leaf (-2)) (.leaf (-1))),
  (.branch 53 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 50 (.branch 45 (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 18 (.branch 11 (.branch 7 (.branch 5 (.leaf (-56)) (.branch 6 (.leaf (-55)) (.leaf (-54)))) (.branch 9 (.branch 8 (.leaf (-53)) (.leaf (-52))) (.branch 10 (.leaf (-51)) (.leaf (-50))))) (.branch 14 (.branch 12 (.leaf (-49)) (.branch 13 (.leaf (-48)) (.leaf (-47)))) (.branch 16 (.branch 15 (.leaf (-46)) (.leaf (-45))) (.branch 17 (.leaf (-44)) (.leaf (-43)))))) (.branch 25 (.branch 21 (.branch 19 (.leaf (-42)) (.branch 20 (.leaf (-41)) (.leaf (-40)))) (.branch 23 (.branch 22 (.leaf (-39)) (.leaf (-38))) (.branch 24 (.leaf (-37)) (.leaf (-36))))) (.branch 28 (.branch 26 (.leaf (-35)) (.branch 27 (.leaf (-34)) (.leaf (-33)))) (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.leaf (-29))))))) (.branch 46 (.branch 39 (.branch 35 (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-27)) (.leaf (-26)))) (.branch 37 (.branch 36 (.leaf (-25)) (.leaf (-24))) (.branch 38 (.leaf (-23)) (.leaf (-22))))) (.branch 42 (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19)))) (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_299_5368 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (8)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (6)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (7)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (8)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (6)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (7)) (.leaf (0))) (.branch 36 (.leaf (4)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (8)) (.leaf (5)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (6)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (7)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (0))) (.branch 55 (.leaf (8)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (6)) (.leaf (4))))))))
  code := certificateP9_5368
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 26 (.leaf (-9)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 41 (.leaf (-6)) (.leaf (-7)))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 51 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-4))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.branch 52 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_299_5369 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (8)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (6)) (.leaf (4))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (5)) (.leaf (1))) (.branch 14 (.leaf (3)) (.leaf (7)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (8))) (.branch 25 (.leaf (0)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (6))) (.branch 29 (.leaf (2)) (.leaf (0))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (3)) (.branch 32 (.leaf (5)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (7))) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (5))) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (4))) (.branch 44 (.leaf (8)) (.leaf (0)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (1)) (.leaf (6)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (0))) (.branch 51 (.leaf (4)) (.leaf (5))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (2))) (.branch 55 (.leaf (7)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (5)) (.leaf (4))))))))
  code := certificateP9_5369
  counts := ![(.branch 25 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 30 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 31 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.leaf (7))))),
  (.branch 34 (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 12 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-39)) (.leaf (-43)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-18))) (.branch 31 (.leaf (-22)) (.leaf (-23)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (-1))) (.branch 51 (.leaf (-2)) (.leaf (-3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (-5))) (.branch 59 (.leaf (-9)) (.leaf (-13)))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 57 (.branch 51 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 48 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 56 (.branch 12 (.leaf (-43)) (.branch 55 (.leaf (-42)) (.leaf (-35)))) (.branch 58 (.branch 57 (.leaf (-28)) (.leaf (-21))) (.branch 59 (.leaf (-14)) (.leaf (-7))))),
  (.branch 58 (.branch 32 (.leaf (-23)) (.leaf (-21))) (.branch 59 (.leaf (-14)) (.leaf (-7)))),
  (.branch 52 (.leaf (-3)) (.leaf (0))),
  (.leaf (-13)),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_299_5370 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (8)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (1))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (7))) (.branch 14 (.leaf (3)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (6)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (5))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (8))) (.branch 25 (.leaf (4)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (7)))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (6)) (.leaf (3))) (.branch 40 (.leaf (5)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (4))) (.branch 44 (.leaf (8)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (6)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (5))) (.branch 51 (.leaf (0)) (.leaf (4))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (7)) (.leaf (2))) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (6))) (.branch 59 (.leaf (4)) (.leaf (5))))))))
  code := certificateP9_5370
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.leaf (7))))),
  (.branch 34 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.branch 19 (.leaf (-17)) (.leaf (-21)))),
  (.branch 5 (.leaf (0)) (.branch 39 (.leaf (-11)) (.leaf (-13)))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (-2))) (.branch 59 (.leaf (-3)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 56 (.leaf (-15)) (.leaf (-12))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3))))),
  (.branch 56 (.branch 46 (.leaf (-21)) (.branch 55 (.leaf (-20)) (.leaf (-17)))) (.branch 58 (.branch 57 (.leaf (-14)) (.leaf (-11))) (.branch 59 (.leaf (-8)) (.leaf (-5))))),
  (.branch 49 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 58 (.leaf (-11)) (.branch 59 (.leaf (-8)) (.leaf (-5))))),
  (.leaf (-5)),
  (.leaf (0)),
  (.branch 48 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_299_5371 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (7)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (6)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (5)) (.leaf (8))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (4)) (.leaf (6))) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (3)) (.leaf (1))) (.branch 44 (.leaf (0)) (.leaf (7)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (5)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (4))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (6)) (.leaf (8))))))))
  code := certificateP9_5371
  counts := ![(.branch 27 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))) (.branch 44 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 48 (.leaf (14)) (.leaf (15))) (.branch 55 (.leaf (16)) (.branch 57 (.leaf (17)) (.leaf (18))))))),
  (.branch 28 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.branch 60 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-12)) (.leaf (-14)))) (.branch 37 (.branch 27 (.leaf (-16)) (.leaf (-18))) (.branch 57 (.leaf (-19)) (.leaf (-21))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 20 (.leaf (-11)) (.branch 50 (.leaf (-14)) (.leaf (-16))))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-16)) (.leaf (-11)))),
  (.branch 55 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 59 (.leaf (-14)) (.leaf (-9)))),
  (.branch 57 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 54 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_299_5372 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (1))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (7)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (5))) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (3))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (4)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (8)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_5372
  counts := ![(.branch 28 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 44 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 48 (.leaf (14)) (.leaf (15))) (.branch 54 (.leaf (16)) (.branch 58 (.leaf (17)) (.leaf (18))))))),
  (.branch 30 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.leaf (15)))))),
  (.branch 29 (.branch 15 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 16 (.leaf (0)) (.leaf (-44))),
  (.branch 36 (.leaf (0)) (.leaf (-24))),
  (.branch 56 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 55 (.leaf (-8)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 50 (.leaf (-1)) (.leaf (0))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 38 (.branch 27 (.branch 21 (.branch 18 (.branch 17 (.leaf (-44)) (.leaf (-43))) (.branch 19 (.leaf (-42)) (.branch 20 (.leaf (-41)) (.leaf (-40))))) (.branch 24 (.branch 22 (.leaf (-39)) (.branch 23 (.leaf (-38)) (.leaf (-37)))) (.branch 25 (.leaf (-36)) (.branch 26 (.leaf (-35)) (.leaf (-34)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (-33)) (.leaf (-32))) (.branch 30 (.leaf (-31)) (.branch 31 (.leaf (-30)) (.leaf (-29))))) (.branch 35 (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-27)) (.leaf (-26)))) (.branch 36 (.leaf (-25)) (.branch 37 (.leaf (-24)) (.leaf (-23))))))) (.branch 49 (.branch 43 (.branch 40 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18))))) (.branch 46 (.branch 44 (.leaf (-17)) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 48 (.branch 42 (.branch 39 (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22)))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_299_5373 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (1)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (1)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (1)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (6)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (1)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (1)) (.leaf (4))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 40 (.leaf (1)) (.leaf (7)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (3))) (.branch 44 (.leaf (1)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (1)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (1)) (.leaf (8)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (4))) (.branch 59 (.leaf (1)) (.leaf (2))))))))
  code := certificateP9_5373
  counts := ![(.branch 27 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 34 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 29 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 15 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-49))),
  (.branch 26 (.leaf (0)) (.leaf (-34))),
  (.branch 41 (.leaf (0)) (.leaf (-19))),
  (.branch 56 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 54 (.branch 50 (.leaf (-14)) (.leaf (-13))) (.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-8)) (.leaf (-4))))),
  (.branch 52 (.branch 48 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.leaf (-4)))),
  (.branch 55 (.leaf (-1)) (.leaf (0))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.branch 23 (.branch 17 (.branch 14 (.branch 12 (.leaf (-49)) (.branch 13 (.leaf (-48)) (.leaf (-47)))) (.branch 15 (.leaf (-46)) (.branch 16 (.leaf (-45)) (.leaf (-44))))) (.branch 20 (.branch 18 (.leaf (-43)) (.branch 19 (.leaf (-42)) (.leaf (-41)))) (.branch 21 (.leaf (-40)) (.branch 22 (.leaf (-39)) (.leaf (-38)))))) (.branch 29 (.branch 26 (.branch 24 (.leaf (-37)) (.branch 25 (.leaf (-36)) (.leaf (-35)))) (.branch 27 (.leaf (-34)) (.branch 28 (.leaf (-33)) (.leaf (-32))))) (.branch 32 (.branch 30 (.leaf (-31)) (.branch 31 (.leaf (-30)) (.leaf (-29)))) (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-27)) (.leaf (-26))))))) (.branch 47 (.branch 41 (.branch 38 (.branch 36 (.leaf (-25)) (.branch 37 (.leaf (-24)) (.leaf (-23)))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))) (.branch 44 (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17)))) (.branch 45 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-34)) (.leaf (-33))) (.branch 29 (.leaf (-32)) (.leaf (-31)))) (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.leaf (-27))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-26)) (.leaf (-25))) (.branch 37 (.leaf (-24)) (.leaf (-23)))) (.branch 40 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18))))))) (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 50 (.branch 45 (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_299_5374 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (5))) (.branch 10 (.leaf (1)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (1)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (8))) (.branch 25 (.leaf (1)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (1)) (.leaf (4))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (6))) (.branch 40 (.leaf (1)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (2))) (.branch 44 (.leaf (1)) (.leaf (4)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (1)) (.leaf (4))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (7))) (.branch 55 (.leaf (1)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_5374
  counts := ![(.branch 27 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 34 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 29 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-51))),
  (.branch 39 (.leaf (0)) (.leaf (-21))),
  (.branch 54 (.leaf (0)) (.leaf (-6))),
  (.branch 24 (.leaf (0)) (.leaf (-36)))]
  high := ![(.branch 54 (.branch 50 (.leaf (-14)) (.leaf (-13))) (.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-8)) (.leaf (-4))))),
  (.branch 52 (.branch 48 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.leaf (-4)))),
  (.branch 51 (.leaf (-5)) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 57 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 34 (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-51)) (.branch 11 (.leaf (-50)) (.leaf (-49)))) (.branch 13 (.leaf (-48)) (.branch 14 (.leaf (-47)) (.leaf (-46))))) (.branch 18 (.branch 16 (.leaf (-45)) (.branch 17 (.leaf (-44)) (.leaf (-43)))) (.branch 19 (.leaf (-42)) (.branch 20 (.leaf (-41)) (.leaf (-40)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-39)) (.branch 23 (.leaf (-38)) (.leaf (-37)))) (.branch 25 (.leaf (-36)) (.branch 26 (.leaf (-35)) (.leaf (-34))))) (.branch 30 (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))) (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.leaf (-27))))))) (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 44 (.branch 41 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17))))) (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-36)) (.leaf (-35))) (.branch 27 (.leaf (-34)) (.leaf (-33)))) (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))))) (.branch 51 (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_299_5375 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (4))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (4))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (1))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (7)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (5))) (.branch 40 (.leaf (4)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (3))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (5)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (8)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (5)) (.leaf (4))))))))
  code := certificateP9_5375
  counts := ![(.branch 28 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 44 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 48 (.leaf (14)) (.leaf (15))) (.branch 54 (.leaf (16)) (.branch 58 (.leaf (17)) (.leaf (18))))))),
  (.branch 30 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.leaf (15)))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 27 (.branch 7 (.leaf (0)) (.leaf (-4))) (.branch 47 (.leaf (-6)) (.leaf (-8)))),
  (.branch 16 (.leaf (0)) (.leaf (-44))),
  (.branch 36 (.leaf (0)) (.leaf (-24))),
  (.branch 56 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 55 (.leaf (-8)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.leaf (-1)) (.leaf (0))),
  (.branch 48 (.leaf (-8)) (.leaf (-7))),
  (.branch 38 (.branch 27 (.branch 21 (.branch 18 (.branch 17 (.leaf (-44)) (.leaf (-43))) (.branch 19 (.leaf (-42)) (.branch 20 (.leaf (-41)) (.leaf (-40))))) (.branch 24 (.branch 22 (.leaf (-39)) (.branch 23 (.leaf (-38)) (.leaf (-37)))) (.branch 25 (.leaf (-36)) (.branch 26 (.leaf (-35)) (.leaf (-34)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (-33)) (.leaf (-32))) (.branch 30 (.leaf (-31)) (.branch 31 (.leaf (-30)) (.leaf (-29))))) (.branch 35 (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-27)) (.leaf (-26)))) (.branch 36 (.leaf (-25)) (.branch 37 (.leaf (-24)) (.leaf (-23))))))) (.branch 49 (.branch 43 (.branch 40 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18))))) (.branch 46 (.branch 44 (.leaf (-17)) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 48 (.branch 42 (.branch 39 (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22)))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_299_5376 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (5))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (6)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (5))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (5)) (.leaf (0))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (7)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (4))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (5)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (3))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (0)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (5)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (8))) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (4)) (.leaf (2))) (.branch 59 (.leaf (0)) (.leaf (5))))))))
  code := certificateP9_5376
  counts := ![(.branch 30 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))) (.branch 44 (.branch 36 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 39 (.leaf (13)) (.branch 41 (.leaf (14)) (.leaf (15))))) (.branch 53 (.branch 47 (.leaf (16)) (.branch 50 (.leaf (17)) (.leaf (18)))) (.branch 56 (.leaf (19)) (.branch 59 (.leaf (20)) (.leaf (21))))))),
  (.branch 28 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 58 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-46))),
  (.branch 34 (.leaf (0)) (.leaf (-26))),
  (.branch 54 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 48 (.branch 42 (.leaf (-13)) (.branch 45 (.leaf (-12)) (.leaf (-11)))) (.branch 54 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.leaf (-7))))),
  (.branch 57 (.branch 49 (.leaf (-16)) (.branch 56 (.leaf (-15)) (.leaf (-12)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3))))),
  (.branch 52 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 50 (.leaf (-1)) (.leaf (0))),
  (.branch 37 (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-46)) (.leaf (-45))) (.branch 17 (.leaf (-44)) (.branch 18 (.leaf (-43)) (.leaf (-42))))) (.branch 22 (.branch 20 (.leaf (-41)) (.branch 21 (.leaf (-40)) (.leaf (-39)))) (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36)))))) (.branch 31 (.branch 28 (.branch 26 (.leaf (-35)) (.branch 27 (.leaf (-34)) (.leaf (-33)))) (.branch 29 (.leaf (-32)) (.branch 30 (.leaf (-31)) (.leaf (-30))))) (.branch 34 (.branch 32 (.leaf (-29)) (.branch 33 (.leaf (-28)) (.leaf (-27)))) (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24))))))) (.branch 48 (.branch 42 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_299_5377 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (6))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (8)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (7))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (6)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (8)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (5))) (.branch 36 (.leaf (2)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (3))) (.branch 40 (.leaf (7)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (4))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (5)) (.branch 47 (.leaf (0)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (6)) (.leaf (3))) (.branch 51 (.leaf (0)) (.leaf (8))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (5)) (.leaf (7))))))))
  code := certificateP9_5377
  counts := ![(.branch 27 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 44 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 47 (.leaf (14)) (.leaf (15))) (.branch 54 (.leaf (16)) (.branch 57 (.leaf (17)) (.leaf (18))))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 26 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 43 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 31 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_299_5378 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (4))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (6))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (5)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (3)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 40 (.leaf (7)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (3))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (5)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (3))) (.branch 51 (.leaf (0)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_5378
  counts := ![(.branch 28 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 44 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 48 (.leaf (14)) (.leaf (15))) (.branch 54 (.leaf (16)) (.branch 58 (.leaf (17)) (.leaf (18))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 15 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 50 (.leaf (7)) (.branch 56 (.leaf (8)) (.leaf (9)))))),
  (.branch 33 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 60 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 20 (.leaf (0)) (.leaf (-40))),
  (.branch 40 (.leaf (0)) (.leaf (-20))),
  (.leaf (0))]
  high := ![(.branch 55 (.leaf (-8)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 58 (.branch 57 (.leaf (-12)) (.leaf (-9))) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-40)) (.leaf (-39))) (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36))))) (.branch 27 (.branch 26 (.leaf (-35)) (.leaf (-34))) (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-27)) (.leaf (-26))))) (.branch 37 (.branch 36 (.leaf (-25)) (.leaf (-24))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))))) (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_299_5379 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (4))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (7)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (5))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (8)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (0))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (0))) (.branch 36 (.leaf (6)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (5)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (3))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (7)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (3))) (.branch 55 (.leaf (0)) (.leaf (8)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (2))) (.branch 59 (.leaf (0)) (.leaf (5))))))))
  code := certificateP9_5379
  counts := ![(.branch 30 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 28 (.leaf (9)) (.leaf (10)))))) (.branch 44 (.branch 35 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 39 (.leaf (13)) (.branch 41 (.leaf (14)) (.leaf (15))))) (.branch 53 (.branch 48 (.leaf (16)) (.branch 50 (.leaf (17)) (.leaf (18)))) (.branch 55 (.leaf (19)) (.branch 59 (.leaf (20)) (.leaf (21))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 58 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 56 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 35 (.leaf (-3)) (.branch 55 (.leaf (-4)) (.leaf (-5))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-24))),
  (.branch 16 (.leaf (0)) (.leaf (-14))),
  (.branch 26 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 56 (.leaf (-5)) (.leaf (-4))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 56 (.branch 44 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 48 (.branch 42 (.branch 39 (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22)))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_299_5380 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (4))) (.branch 10 (.leaf (2)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (7)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (8)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (6)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (5))) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (3))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (7)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (8)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_5380
  counts := ![(.branch 28 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 44 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 48 (.leaf (14)) (.leaf (15))) (.branch 54 (.leaf (16)) (.branch 58 (.leaf (17)) (.leaf (18))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 56 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-24))),
  (.branch 16 (.leaf (0)) (.leaf (-14))),
  (.branch 26 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 55 (.leaf (-8)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 48 (.branch 42 (.branch 39 (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22)))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_299_5381 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (2)) (.leaf (7))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (6))) (.branch 21 (.leaf (2)) (.leaf (8))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (4))) (.branch 36 (.leaf (2)) (.leaf (7))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (6)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (3)) (.leaf (2))) (.branch 44 (.leaf (0)) (.leaf (4)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (2)) (.leaf (8))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (4)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (2))) (.branch 59 (.leaf (0)) (.leaf (6))))))))
  code := certificateP9_5381
  counts := ![(.branch 29 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 44 (.branch 34 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 38 (.leaf (12)) (.branch 41 (.leaf (13)) (.leaf (14))))) (.branch 53 (.branch 46 (.leaf (15)) (.branch 49 (.leaf (16)) (.leaf (17)))) (.branch 56 (.leaf (18)) (.branch 59 (.leaf (19)) (.leaf (20))))))),
  (.branch 24 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-3)) (.leaf (-4)))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 33 (.leaf (-6)) (.branch 48 (.leaf (-7)) (.leaf (-8))))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 22 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 50 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-10)) (.leaf (-8)))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 59 (.leaf (-4)) (.leaf (-2))),
  (.branch 58 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 48 (.branch 42 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_299_5382 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (6))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (4))) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (7))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (6))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (4))) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (5)) (.leaf (0))) (.branch 44 (.leaf (3)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (8))) (.branch 51 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (3))) (.branch 55 (.leaf (0)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (5)) (.leaf (0))) (.branch 59 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_5382
  counts := ![(.branch 28 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 40 (.leaf (13)) (.leaf (14))))) (.branch 52 (.branch 46 (.leaf (15)) (.branch 49 (.leaf (16)) (.leaf (17)))) (.branch 55 (.leaf (18)) (.branch 58 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-25))),
  (.branch 20 (.leaf (0)) (.leaf (-40))),
  (.branch 50 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 56 (.branch 34 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.leaf (-2)) (.leaf (-1))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.branch 41 (.branch 38 (.branch 36 (.leaf (-25)) (.branch 37 (.leaf (-24)) (.leaf (-23)))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))) (.branch 44 (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17)))) (.branch 45 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-40)) (.leaf (-39))) (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36))))) (.branch 27 (.branch 26 (.leaf (-35)) (.leaf (-34))) (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-27)) (.leaf (-26))))) (.branch 37 (.branch 36 (.leaf (-25)) (.leaf (-24))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))))) (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_299_5383 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (6)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (3))) (.branch 14 (.leaf (2)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (4))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (7)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (4)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 40 (.leaf (6)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (3))) (.branch 44 (.leaf (2)) (.leaf (0)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (5)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (4))) (.branch 51 (.leaf (0)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (8)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_5383
  counts := ![(.branch 28 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))) (.branch 45 (.branch 35 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 48 (.leaf (14)) (.leaf (15))) (.branch 55 (.leaf (16)) (.branch 58 (.leaf (17)) (.leaf (18))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-20))),
  (.branch 26 (.leaf (0)) (.leaf (-34))),
  (.branch 56 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 52 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-34)) (.leaf (-33))) (.branch 29 (.leaf (-32)) (.leaf (-31)))) (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.leaf (-27))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-26)) (.leaf (-25))) (.branch 37 (.leaf (-24)) (.leaf (-23)))) (.branch 40 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18))))))) (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_299_5384 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (8)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (5)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (6)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (7)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (5)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (6)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (3)) (.leaf (0))) (.branch 40 (.leaf (2)) (.leaf (4)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (8)) (.leaf (5)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (6)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (5)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (7)) (.leaf (6))))))))
  code := certificateP9_5384
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.leaf (0)) (.branch 59 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-4)) (.leaf (-6)))) (.branch 40 (.leaf (-7)) (.branch 55 (.leaf (-8)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.branch 26 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.branch 41 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 29 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 51 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-4))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5))))),
  (.branch 55 (.branch 52 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_299_5385 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (0))) (.branch 10 (.leaf (7)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (6)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (8)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (2)) (.leaf (7))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (4)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (6)) (.leaf (0))) (.branch 40 (.leaf (8)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (3))) (.branch 44 (.leaf (1)) (.leaf (4)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (7)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (6))) (.branch 59 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_5385
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-8)) (.leaf (-4)))),
  (.branch 57 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.leaf (-2)) (.leaf (-1))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 55 (.branch 52 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_299_5386 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (6)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (4)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (7)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (5)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (4)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (6)) (.leaf (0))) (.branch 40 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (5)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (4)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (8)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_5386
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 53 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-22))),
  (.branch 23 (.leaf (0)) (.leaf (-37))),
  (.branch 53 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 51 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-4))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 50 (.leaf (-1)) (.leaf (0))),
  (.branch 57 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 49 (.branch 43 (.branch 40 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18))))) (.branch 46 (.branch 44 (.leaf (-17)) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 41 (.branch 32 (.branch 27 (.branch 25 (.branch 24 (.leaf (-37)) (.leaf (-36))) (.branch 26 (.leaf (-35)) (.leaf (-34)))) (.branch 29 (.branch 28 (.leaf (-33)) (.leaf (-32))) (.branch 30 (.leaf (-31)) (.branch 31 (.leaf (-30)) (.leaf (-29)))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 35 (.leaf (-26)) (.leaf (-25)))) (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-23))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))))) (.branch 50 (.branch 45 (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_299_5387 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (6))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (3))) (.branch 21 (.leaf (5)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (7))) (.branch 29 (.leaf (3)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (5)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (3)) (.leaf (0))) (.branch 40 (.leaf (2)) (.leaf (4)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (6))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (3))) (.branch 55 (.leaf (2)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (8))) (.branch 59 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_5387
  counts := ![(.branch 26 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 44 (.branch 35 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 39 (.leaf (9)) (.leaf (10)))) (.branch 53 (.branch 48 (.leaf (11)) (.leaf (12))) (.branch 56 (.leaf (13)) (.leaf (14)))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 58 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))) (.branch 26 (.leaf (-12)) (.branch 56 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 54 (.leaf (-19)) (.leaf (-20)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (-2))) (.branch 24 (.leaf (-4)) (.branch 41 (.leaf (-6)) (.leaf (-7))))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 13 (.leaf (0)) (.leaf (-17))),
  (.branch 28 (.leaf (0)) (.leaf (-32))),
  (.branch 58 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 58 (.branch 57 (.leaf (-14)) (.leaf (-11))) (.branch 59 (.leaf (-8)) (.leaf (-5)))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 50 (.leaf (-1)) (.leaf (0))),
  (.branch 57 (.branch 55 (.leaf (-20)) (.branch 56 (.leaf (-17)) (.leaf (-14)))) (.branch 58 (.leaf (-11)) (.branch 59 (.leaf (-8)) (.leaf (-5))))),
  (.branch 42 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.leaf (-29)))) (.branch 34 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 35 (.leaf (-26)) (.leaf (-25))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-23))) (.branch 39 (.leaf (-22)) (.leaf (-21)))) (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.leaf (-17)))))) (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_299_5388 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (7))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (6)) (.leaf (3))) (.branch 14 (.leaf (1)) (.leaf (8)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (1)) (.leaf (7))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (6))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (8))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (4)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (5)) (.leaf (3))) (.branch 44 (.leaf (1)) (.leaf (8)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (6)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (1)) (.leaf (7))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (5))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (4))) (.branch 59 (.leaf (6)) (.leaf (8))))))))
  code := certificateP9_5388
  counts := ![(.branch 25 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-6)) (.leaf (-7)))),
  (.branch 47 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-6))) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 56 (.branch 30 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessP9_299_5389 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (7)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (8)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (6)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (7)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (6)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (8)) (.leaf (5)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (4)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (7)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (6)) (.leaf (0))) (.branch 55 (.leaf (5)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (8)) (.leaf (4))))))))
  code := certificateP9_5389
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 34 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 26 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 21 (.leaf (-6)) (.leaf (-7)))) (.branch 51 (.branch 38 (.leaf (-9)) (.leaf (-11))) (.branch 56 (.leaf (-12)) (.leaf (-14))))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 36 (.leaf (-10)) (.leaf (-12)))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (-10)) (.leaf (-11)))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 51 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-4))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 58 (.branch 57 (.leaf (-14)) (.leaf (-13))) (.branch 59 (.leaf (-12)) (.leaf (-11)))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.leaf (-1)) (.leaf (0))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 54 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9)))) (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5))))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_299_5390 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (7)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (1))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (6))) (.branch 21 (.leaf (8)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (7)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (4)) (.leaf (1))) (.branch 40 (.leaf (6)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (0))) (.branch 44 (.leaf (3)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (0)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (8)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (3))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (4)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (6))))))))
  code := certificateP9_5390
  counts := ![(.branch 29 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 41 (.leaf (13)) (.leaf (14))))) (.branch 53 (.branch 47 (.leaf (15)) (.branch 49 (.leaf (16)) (.leaf (17)))) (.branch 55 (.leaf (18)) (.branch 59 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 32 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 32 (.leaf (-13)) (.leaf (-18)))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 48 (.leaf (-15)) (.leaf (-17)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (-5))) (.branch 46 (.leaf (-10)) (.leaf (-13)))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-24))),
  (.branch 21 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 56 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.branch 33 (.leaf (-18)) (.leaf (-17))) (.branch 59 (.leaf (-16)) (.leaf (-13)))),
  (.branch 57 (.branch 49 (.leaf (-17)) (.leaf (-16))) (.branch 58 (.leaf (-13)) (.branch 59 (.leaf (-10)) (.leaf (-7))))),
  (.branch 56 (.branch 34 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 47 (.leaf (-13)) (.leaf (-12))) (.branch 59 (.leaf (-10)) (.leaf (-8)))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 48 (.branch 42 (.branch 39 (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22)))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_299_5391 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (7)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (4)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (6)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (8)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (4)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (5)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (6)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (4)) (.leaf (5))))))))
  code := certificateP9_5391
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 34 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.leaf (0)) (.branch 53 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 26 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 21 (.leaf (-6)) (.leaf (-7)))) (.branch 51 (.branch 38 (.leaf (-9)) (.leaf (-11))) (.branch 56 (.leaf (-12)) (.leaf (-14))))),
  (.branch 3 (.leaf (0)) (.branch 25 (.leaf (-9)) (.leaf (-10)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 23 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-54))),
  (.branch 36 (.leaf (0)) (.leaf (-24)))]
  high := ![(.branch 51 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-4))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 58 (.branch 57 (.leaf (-14)) (.leaf (-13))) (.branch 59 (.leaf (-12)) (.leaf (-11)))),
  (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-1)),
  (.branch 45 (.leaf (-1)) (.leaf (0))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 19 (.branch 12 (.branch 9 (.branch 7 (.leaf (-54)) (.branch 8 (.leaf (-53)) (.leaf (-52)))) (.branch 10 (.leaf (-51)) (.branch 11 (.leaf (-50)) (.leaf (-49))))) (.branch 15 (.branch 13 (.leaf (-48)) (.branch 14 (.leaf (-47)) (.leaf (-46)))) (.branch 17 (.branch 16 (.leaf (-45)) (.leaf (-44))) (.branch 18 (.leaf (-43)) (.leaf (-42)))))) (.branch 26 (.branch 22 (.branch 20 (.leaf (-41)) (.branch 21 (.leaf (-40)) (.leaf (-39)))) (.branch 24 (.branch 23 (.leaf (-38)) (.leaf (-37))) (.branch 25 (.leaf (-36)) (.leaf (-35))))) (.branch 29 (.branch 27 (.leaf (-34)) (.branch 28 (.leaf (-33)) (.leaf (-32)))) (.branch 31 (.branch 30 (.leaf (-31)) (.leaf (-30))) (.branch 32 (.leaf (-29)) (.leaf (-28))))))) (.branch 46 (.branch 39 (.branch 36 (.branch 34 (.leaf (-27)) (.branch 35 (.leaf (-26)) (.leaf (-25)))) (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22))))) (.branch 42 (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19)))) (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))))) (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 48 (.branch 42 (.branch 39 (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22)))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_299_5392 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (7)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (5)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (6)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (8)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (5)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (7)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (6)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (4)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (5)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (8)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (6)) (.leaf (4))))))))
  code := certificateP9_5392
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 34 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.branch 53 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 26 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 21 (.leaf (-6)) (.leaf (-7)))) (.branch 51 (.branch 38 (.leaf (-9)) (.leaf (-11))) (.branch 56 (.leaf (-12)) (.leaf (-14))))),
  (.branch 3 (.leaf (0)) (.branch 25 (.leaf (-9)) (.leaf (-10)))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (-10)) (.leaf (-11)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-24))),
  (.branch 23 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 51 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-4))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 58 (.branch 57 (.leaf (-14)) (.leaf (-13))) (.branch 59 (.leaf (-12)) (.leaf (-11)))),
  (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 45 (.leaf (-1)) (.leaf (0))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 48 (.branch 42 (.branch 39 (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22)))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_299_5393 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (7)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (1))) (.branch 14 (.leaf (3)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (8)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (6))) (.branch 21 (.leaf (4)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (7)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (8)) (.leaf (4))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (6)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (1))) (.branch 44 (.leaf (3)) (.leaf (0)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (7)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (5))) (.branch 51 (.leaf (4)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (8)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (6))))))))
  code := certificateP9_5393
  counts := ![(.branch 29 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))) (.branch 45 (.branch 35 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 52 (.branch 48 (.leaf (14)) (.leaf (15))) (.branch 55 (.leaf (16)) (.branch 59 (.leaf (17)) (.leaf (18))))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 32 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 31 (.leaf (-13)) (.branch 41 (.leaf (-15)) (.leaf (-16))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-5)) (.leaf (-7)))) (.branch 43 (.branch 32 (.leaf (-8)) (.leaf (-10))) (.branch 47 (.leaf (-11)) (.branch 58 (.leaf (-13)) (.leaf (-14)))))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (-8)) (.leaf (-9)))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 49 (.branch 42 (.leaf (-16)) (.leaf (-15))) (.branch 56 (.leaf (-14)) (.leaf (-11)))),
  (.branch 59 (.leaf (-14)) (.leaf (-13))),
  (.branch 58 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_299_5394 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (2))) (.branch 10 (.leaf (8)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (4))) (.branch 14 (.leaf (2)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (7))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (2))) (.branch 25 (.leaf (5)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (4))) (.branch 29 (.leaf (2)) (.leaf (8))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (6))) (.branch 36 (.leaf (0)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (3)) (.leaf (2))) (.branch 40 (.leaf (7)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (4))) (.branch 44 (.leaf (2)) (.leaf (5)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (8))) (.branch 51 (.leaf (0)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (2))) (.branch 55 (.leaf (6)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (4))) (.branch 59 (.leaf (2)) (.leaf (7))))))))
  code := certificateP9_5394
  counts := ![(.branch 26 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-6)) (.leaf (-10)))) (.branch 38 (.leaf (-13)) (.branch 53 (.leaf (-16)) (.leaf (-19))))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 56 (.branch 54 (.leaf (-19)) (.branch 55 (.leaf (-18)) (.leaf (-17)))) (.branch 58 (.branch 57 (.leaf (-16)) (.leaf (-15))) (.branch 59 (.leaf (-14)) (.leaf (-13))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_299_5395 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (5))) (.branch 6 (.leaf (6)) (.leaf (7))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (4)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (8)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (6)) (.leaf (4))) (.branch 21 (.leaf (3)) (.leaf (7))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (3)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (8)) (.branch 32 (.leaf (6)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (5)) (.leaf (7))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (3)) (.leaf (0))) (.branch 40 (.leaf (4)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (6))) (.branch 44 (.leaf (0)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (8)) (.branch 47 (.leaf (5)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (4))) (.branch 51 (.leaf (0)) (.leaf (7))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (6)) (.leaf (3))) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (5))) (.branch 59 (.leaf (8)) (.leaf (4))))))))
  code := certificateP9_5395
  counts := ![(.branch 27 (.branch 13 (.branch 1 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 51 (.leaf (9)) (.branch 56 (.leaf (10)) (.leaf (11)))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 27 (.leaf (-7)) (.branch 44 (.leaf (-9)) (.leaf (-10))))),
  (.branch 28 (.branch 2 (.leaf (0)) (.leaf (-24))) (.branch 48 (.leaf (-30)) (.leaf (-32)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 18 (.leaf (-13)) (.branch 33 (.leaf (-15)) (.leaf (-16))))),
  (.branch 29 (.branch 3 (.leaf (0)) (.leaf (-23))) (.branch 45 (.leaf (-24)) (.leaf (-30)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-23)) (.leaf (-30)))),
  (.branch 43 (.branch 6 (.leaf (0)) (.leaf (-20))) (.branch 53 (.leaf (-23)) (.leaf (-31)))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 15 (.leaf (0)) (.branch 59 (.leaf (-1)) (.leaf (-6))))]
  high := ![(.branch 58 (.branch 57 (.leaf (-10)) (.leaf (-9))) (.branch 59 (.leaf (-8)) (.leaf (-7)))),
  (.branch 57 (.branch 49 (.leaf (-32)) (.branch 56 (.leaf (-31)) (.leaf (-26)))) (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-16)) (.leaf (-11))))),
  (.branch 50 (.branch 34 (.leaf (-16)) (.branch 42 (.leaf (-15)) (.leaf (-14)))) (.branch 58 (.leaf (-13)) (.branch 59 (.leaf (-10)) (.leaf (-7))))),
  (.branch 56 (.branch 46 (.leaf (-30)) (.branch 55 (.leaf (-29)) (.leaf (-25)))) (.branch 58 (.branch 57 (.leaf (-21)) (.leaf (-17))) (.branch 59 (.leaf (-13)) (.leaf (-9))))),
  (.leaf (0)),
  (.branch 37 (.branch 15 (.leaf (-30)) (.branch 26 (.leaf (-29)) (.leaf (-28)))) (.branch 48 (.leaf (-27)) (.branch 59 (.leaf (-26)) (.leaf (-22))))),
  (.branch 56 (.branch 54 (.leaf (-31)) (.branch 55 (.leaf (-28)) (.leaf (-25)))) (.branch 58 (.branch 57 (.leaf (-22)) (.leaf (-19))) (.branch 59 (.leaf (-16)) (.leaf (-13))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-6))]
def witnessP9_299_5396 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (7))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (0))) (.branch 10 (.leaf (4)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (8)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (4)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (7))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (3))) (.branch 29 (.leaf (0)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (8))) (.branch 36 (.leaf (0)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (5)) (.leaf (0))) (.branch 40 (.leaf (3)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (7)) (.leaf (4)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (6)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (8))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (4))) (.branch 59 (.leaf (0)) (.leaf (6))))))))
  code := certificateP9_5396
  counts := ![(.branch 29 (.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 36 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 20 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 31 (.leaf (-4)) (.branch 50 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 51 (.leaf (-6)) (.leaf (-5))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-6))) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_299_5397 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (0))) (.branch 10 (.leaf (6)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (1)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (8)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (5))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (6)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (7))) (.branch 29 (.leaf (4)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (0))) (.branch 36 (.leaf (2)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (8)) (.leaf (0))) (.branch 40 (.leaf (6)) (.leaf (4)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (3))) (.branch 44 (.leaf (1)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (5)) (.leaf (7)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (4))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (6)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (8))) (.branch 59 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_5397
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (-2))) (.branch 36 (.leaf (-3)) (.branch 51 (.leaf (-4)) (.leaf (-5))))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-8)) (.leaf (-4)))),
  (.branch 57 (.branch 50 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 52 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))) (.branch 55 (.leaf (-2)) (.branch 56 (.leaf (-1)) (.leaf (0))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_299_5398 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (5))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (2)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (7))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (3))) (.branch 29 (.leaf (5)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (0))) (.branch 36 (.leaf (2)) (.leaf (6))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (5))) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (2))) (.branch 44 (.leaf (1)) (.leaf (0)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (2)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (8))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (4)) (.leaf (3))) (.branch 59 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_5398
  counts := ![(.branch 25 (.branch 11 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 36 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 33 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 47 (.leaf (-7)) (.leaf (-12)))),
  (.branch 28 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 33 (.leaf (-11)) (.branch 58 (.leaf (-15)) (.leaf (-16))))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 22 (.leaf (0)) (.leaf (-38))),
  (.branch 52 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.branch 48 (.leaf (-12)) (.leaf (-9))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-1)) (.leaf (0))))),
  (.branch 59 (.leaf (-16)) (.leaf (-13))),
  (.branch 58 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 49 (.leaf (-2)) (.leaf (-1))),
  (.branch 48 (.branch 42 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 41 (.branch 31 (.branch 26 (.branch 24 (.branch 23 (.leaf (-38)) (.leaf (-37))) (.branch 25 (.leaf (-36)) (.leaf (-35)))) (.branch 28 (.branch 27 (.leaf (-34)) (.leaf (-33))) (.branch 29 (.leaf (-32)) (.branch 30 (.leaf (-31)) (.leaf (-30)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-29)) (.leaf (-28))) (.branch 34 (.leaf (-27)) (.branch 35 (.leaf (-26)) (.leaf (-25))))) (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-23))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))))) (.branch 50 (.branch 45 (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_299_5399 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (7))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (6)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (8)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (5))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (7)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (0))) (.branch 36 (.leaf (1)) (.leaf (8))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (5)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (4)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (7)) (.branch 47 (.leaf (0)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (6))) (.branch 51 (.leaf (0)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (8)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_5399
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 29 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 59 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 31 (.leaf (-14)) (.leaf (-16)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-19))) (.branch 48 (.leaf (-22)) (.leaf (-24)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-3))) (.branch 18 (.leaf (-6)) (.branch 38 (.leaf (-9)) (.leaf (-10))))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (-6)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 7 (.leaf (0)) (.branch 46 (.leaf (-13)) (.leaf (-14)))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 55 (.branch 32 (.leaf (-16)) (.leaf (-15))) (.branch 59 (.leaf (-14)) (.leaf (-9)))),
  (.branch 57 (.branch 49 (.leaf (-24)) (.branch 56 (.leaf (-23)) (.leaf (-19)))) (.branch 58 (.leaf (-15)) (.branch 59 (.leaf (-11)) (.leaf (-7))))),
  (.branch 46 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.leaf (-7)))),
  (.branch 57 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_299_5400 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (7))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (5))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (2)) (.leaf (6)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (8))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (3))) (.branch 29 (.leaf (5)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (0))) (.branch 36 (.leaf (2)) (.leaf (7))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (6))) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (2))) (.branch 44 (.leaf (1)) (.leaf (0)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (2)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (8))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (4)) (.leaf (3))) (.branch 59 (.leaf (6)) (.leaf (2))))))))
  code := certificateP9_5400
  counts := ![(.branch 25 (.branch 11 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 36 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 33 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 47 (.leaf (-7)) (.leaf (-12)))),
  (.branch 28 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 33 (.leaf (-11)) (.branch 58 (.leaf (-15)) (.leaf (-16))))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.branch 48 (.leaf (-11)) (.leaf (-12)))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 22 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.branch 48 (.leaf (-12)) (.leaf (-9))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-1)) (.leaf (0))))),
  (.branch 59 (.leaf (-16)) (.leaf (-13))),
  (.branch 58 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 48 (.branch 42 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_299_5401 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (3)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (6))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (5)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (4)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (7))) (.branch 29 (.leaf (3)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (0))) (.branch 36 (.leaf (5)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (0))) (.branch 40 (.leaf (3)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (6))) (.branch 44 (.leaf (1)) (.leaf (4)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (5)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (4)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (8))) (.branch 59 (.leaf (3)) (.leaf (2))))))))
  code := certificateP9_5401
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 11 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 37 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 33 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 58 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 19 (.leaf (-16)) (.branch 49 (.leaf (-19)) (.leaf (-21))))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.branch 41 (.leaf (-6)) (.leaf (-11)))),
  (.branch 22 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 33 (.leaf (-8)) (.branch 52 (.leaf (-12)) (.leaf (-13))))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 13 (.leaf (0)) (.leaf (-17))),
  (.branch 28 (.leaf (0)) (.leaf (-32))),
  (.branch 58 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 54 (.branch 50 (.leaf (-21)) (.leaf (-20))) (.branch 58 (.leaf (-19)) (.branch 59 (.leaf (-14)) (.leaf (-9))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.branch 42 (.leaf (-11)) (.leaf (-9))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-1)) (.leaf (0))))),
  (.branch 53 (.leaf (-13)) (.leaf (-12))),
  (.branch 57 (.branch 35 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.leaf (-29)))) (.branch 34 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 35 (.leaf (-26)) (.leaf (-25))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-23))) (.branch 39 (.leaf (-22)) (.leaf (-21)))) (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.leaf (-17)))))) (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_299_5402 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (3)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (6)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (5)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (7)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (3))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (5)) (.leaf (4))) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (3))) (.branch 44 (.leaf (4)) (.leaf (0)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (5)) (.branch 47 (.leaf (2)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (4)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (8))) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (5))) (.branch 59 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_5402
  counts := ![(.branch 29 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.leaf (15)))))),
  (.branch 28 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 33 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 60 (.leaf (8)) (.leaf (9)))))),
  (.branch 30 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 37 (.leaf (5)) (.leaf (6))) (.branch 50 (.leaf (7)) (.branch 57 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 59 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 44 (.leaf (-4)) (.leaf (-5)))),
  (.branch 26 (.branch 6 (.leaf (0)) (.leaf (-5))) (.branch 46 (.leaf (-7)) (.leaf (-9)))),
  (.branch 14 (.leaf (0)) (.leaf (-46))),
  (.branch 34 (.leaf (0)) (.leaf (-26))),
  (.branch 54 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 49 (.leaf (-16)) (.branch 56 (.leaf (-15)) (.leaf (-12)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3))))),
  (.branch 54 (.leaf (-1)) (.leaf (0))),
  (.branch 51 (.branch 44 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3))))),
  (.branch 52 (.leaf (-5)) (.leaf (-4))),
  (.branch 47 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7)))),
  (.branch 37 (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-46)) (.leaf (-45))) (.branch 17 (.leaf (-44)) (.branch 18 (.leaf (-43)) (.leaf (-42))))) (.branch 22 (.branch 20 (.leaf (-41)) (.branch 21 (.leaf (-40)) (.leaf (-39)))) (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36)))))) (.branch 31 (.branch 28 (.branch 26 (.leaf (-35)) (.branch 27 (.leaf (-34)) (.leaf (-33)))) (.branch 29 (.leaf (-32)) (.branch 30 (.leaf (-31)) (.leaf (-30))))) (.branch 34 (.branch 32 (.leaf (-29)) (.branch 33 (.leaf (-28)) (.leaf (-27)))) (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24))))))) (.branch 48 (.branch 42 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_299_5403 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (7))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (6)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (8))) (.branch 21 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (1))) (.branch 25 (.leaf (3)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (7))) (.branch 29 (.leaf (1)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (5)) (.leaf (8))) (.branch 40 (.leaf (1)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (2))) (.branch 44 (.leaf (6)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (7))) (.branch 51 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (2))) (.branch 55 (.leaf (3)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (8))) (.branch 59 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_5403
  counts := ![(.branch 27 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 51 (.leaf (9)) (.branch 56 (.leaf (10)) (.leaf (11)))))),
  (.branch 32 (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 54 (.leaf (9)) (.branch 59 (.leaf (10)) (.leaf (11)))))),
  (.branch 25 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-38))) (.branch 45 (.leaf (-43)) (.leaf (-45)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 15 (.leaf (-10)) (.leaf (-15)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (-14))) (.branch 47 (.leaf (-18)) (.leaf (-20)))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (-12)) (.leaf (-14)))),
  (.branch 39 (.branch 20 (.leaf (0)) (.leaf (-1))) (.branch 58 (.leaf (-3)) (.leaf (-5))))]
  high := ![(.branch 58 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 46 (.leaf (-45)) (.leaf (-44))) (.branch 58 (.leaf (-33)) (.branch 59 (.leaf (-22)) (.leaf (-11))))),
  (.branch 27 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 38 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11))))),
  (.branch 57 (.branch 48 (.leaf (-20)) (.branch 56 (.leaf (-19)) (.leaf (-16)))) (.branch 58 (.leaf (-13)) (.branch 59 (.leaf (-10)) (.leaf (-7))))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.leaf (-1)) (.leaf (0))),
  (.branch 54 (.branch 51 (.branch 29 (.leaf (-14)) (.leaf (-13))) (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-11)) (.leaf (-10))))) (.branch 57 (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-8)) (.leaf (-7)))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 59 (.leaf (-5)) (.leaf (-4)))]
def witnessP9_299_5404 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (5))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (1))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (6))) (.branch 14 (.leaf (4)) (.leaf (8)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (5))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (7)) (.leaf (4))) (.branch 25 (.leaf (3)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (1)) (.leaf (8))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (7)) (.leaf (2))) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (6))) (.branch 44 (.leaf (4)) (.leaf (8)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (5))) (.branch 51 (.leaf (0)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (7)) (.leaf (4))) (.branch 55 (.leaf (3)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (6))) (.branch 59 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_5404
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 56 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 59 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 58 (.branch 52 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 43 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3))))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessP9_299_5405 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (7))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (6)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (2)) (.leaf (8)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (3))) (.branch 29 (.leaf (7)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (0))) (.branch 36 (.leaf (2)) (.leaf (4))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (8))) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (6)) (.leaf (2))) (.branch 44 (.leaf (1)) (.leaf (0)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (2)) (.leaf (7)))) (.branch 50 (.branch 49 (.leaf (5)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (4))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (6)) (.leaf (3))) (.branch 59 (.leaf (8)) (.leaf (2))))))))
  code := certificateP9_5405
  counts := ![(.branch 25 (.branch 11 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 36 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 33 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 47 (.leaf (-7)) (.leaf (-12)))),
  (.branch 28 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 33 (.leaf (-11)) (.branch 58 (.leaf (-15)) (.leaf (-16))))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.branch 48 (.leaf (-11)) (.leaf (-12)))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.branch 48 (.leaf (-12)) (.leaf (-9))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-1)) (.leaf (0))))),
  (.branch 59 (.leaf (-16)) (.leaf (-13))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_299_5406 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (3)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (7))) (.branch 14 (.leaf (1)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (4)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (5)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (8))) (.branch 29 (.leaf (3)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (0))) (.branch 36 (.leaf (4)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (0))) (.branch 40 (.leaf (3)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (7))) (.branch 44 (.leaf (1)) (.leaf (5)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (4)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (6)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (8))) (.branch 59 (.leaf (3)) (.leaf (2))))))))
  code := certificateP9_5406
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 11 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 37 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 33 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 58 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 19 (.leaf (-16)) (.branch 49 (.leaf (-19)) (.leaf (-21))))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.branch 41 (.leaf (-6)) (.leaf (-11)))),
  (.branch 22 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 33 (.leaf (-8)) (.branch 52 (.leaf (-12)) (.leaf (-13))))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 15 (.leaf (0)) (.branch 34 (.leaf (-5)) (.leaf (-6)))),
  (.branch 13 (.leaf (0)) (.leaf (-17))),
  (.branch 28 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 54 (.branch 50 (.leaf (-21)) (.leaf (-20))) (.branch 58 (.leaf (-19)) (.branch 59 (.leaf (-14)) (.leaf (-9))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.branch 42 (.leaf (-11)) (.leaf (-9))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-1)) (.leaf (0))))),
  (.branch 53 (.leaf (-13)) (.leaf (-12))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.branch 48 (.branch 46 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 35 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_299_5407 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (7)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (2))) (.branch 14 (.leaf (5)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (6)) (.leaf (8))) (.branch 21 (.leaf (3)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (1)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (3)) (.leaf (7))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (3)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (8)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (2))) (.branch 44 (.leaf (5)) (.leaf (0)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (6)) (.leaf (7))) (.branch 51 (.leaf (4)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (5))) (.branch 55 (.leaf (1)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (4)) (.leaf (8))))))))
  code := certificateP9_5407
  counts := ![(.branch 27 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 45 (.branch 36 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 40 (.leaf (9)) (.leaf (10)))) (.branch 53 (.branch 48 (.leaf (11)) (.leaf (12))) (.branch 57 (.leaf (13)) (.leaf (14)))))),
  (.branch 25 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 48 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-1)) (.leaf (-3)))) (.branch 43 (.leaf (-4)) (.branch 58 (.leaf (-5)) (.leaf (-6))))),
  (.branch 29 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 46 (.leaf (-7)) (.leaf (-8)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (-1))) (.branch 33 (.leaf (-2)) (.branch 59 (.leaf (-3)) (.leaf (-4))))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-10)) (.leaf (-11)))),
  (.branch 11 (.leaf (0)) (.branch 30 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0))]
  high := ![(.branch 58 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 59 (.leaf (-8)) (.leaf (-5)))),
  (.branch 56 (.branch 40 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-6))) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 59 (.leaf (-6)) (.leaf (-5))),
  (.branch 57 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-5)) (.leaf (-4))))),
  (.leaf (-4)),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_299_5408 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (6))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (1))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (8))) (.branch 14 (.leaf (5)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (6))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (3)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (7))) (.branch 29 (.leaf (1)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (4)) (.leaf (2))) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (8))) (.branch 44 (.leaf (5)) (.leaf (4)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (6))) (.branch 51 (.leaf (0)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (3)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (7))) (.branch 59 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_5408
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 56 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 59 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.leaf (0)) (.branch 58 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 28 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 58 (.branch 52 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 43 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3))))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 51 (.branch 47 (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_299_5409 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (6)))) (.branch 20 (.branch 19 (.leaf (8)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (1))) (.branch 29 (.leaf (5)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (7)) (.leaf (0))) (.branch 36 (.leaf (2)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (6)) (.leaf (0))) (.branch 40 (.leaf (2)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (3))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (8)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (4)) (.leaf (1))) (.branch 59 (.leaf (6)) (.leaf (2))))))))
  code := certificateP9_5409
  counts := ![(.branch 26 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 44 (.branch 35 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 39 (.leaf (9)) (.leaf (10)))) (.branch 52 (.branch 47 (.leaf (11)) (.leaf (12))) (.branch 56 (.leaf (13)) (.leaf (14)))))),
  (.branch 28 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 46 (.branch 37 (.branch 32 (.leaf (7)) (.leaf (8))) (.branch 41 (.leaf (9)) (.leaf (10)))) (.branch 54 (.branch 50 (.leaf (11)) (.leaf (12))) (.branch 58 (.leaf (13)) (.leaf (14)))))),
  (.branch 30 (.branch 15 (.branch 6 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 36 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))) (.branch 17 (.leaf (-12)) (.branch 47 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.branch 32 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-26))),
  (.branch 19 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 57 (.branch 48 (.leaf (-15)) (.leaf (-14))) (.branch 58 (.leaf (-11)) (.branch 59 (.leaf (-8)) (.leaf (-5))))),
  (.branch 59 (.leaf (-8)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_299_5410 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (4))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (1))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (4))) (.branch 14 (.leaf (8)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (4))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (7))) (.branch 25 (.leaf (3)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (1)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (8)) (.leaf (4))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (5)) (.leaf (2))) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (4))) (.branch 44 (.leaf (7)) (.leaf (6)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (4))) (.branch 51 (.leaf (0)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (8))) (.branch 55 (.leaf (3)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (4))) (.branch 59 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_5410
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 56 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 59 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 58 (.branch 52 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 43 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3))))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 51 (.leaf (-5)) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_299_5411 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (8)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (4))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (6)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (7)) (.leaf (4))) (.branch 21 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (1))) (.branch 25 (.leaf (3)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (1)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (8)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (5)) (.leaf (4))) (.branch 40 (.leaf (1)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (2))) (.branch 44 (.leaf (6)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (7)) (.leaf (4))) (.branch 51 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (5)) (.leaf (2))) (.branch 55 (.leaf (3)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (4))) (.branch 59 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_5411
  counts := ![(.branch 27 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 51 (.leaf (9)) (.branch 56 (.leaf (10)) (.leaf (11)))))),
  (.branch 32 (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 54 (.leaf (9)) (.branch 59 (.leaf (10)) (.leaf (11)))))),
  (.branch 25 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-38))) (.branch 45 (.leaf (-43)) (.leaf (-45)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 15 (.leaf (-10)) (.leaf (-15)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (-14))) (.branch 47 (.leaf (-18)) (.leaf (-20)))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (-3))) (.branch 58 (.leaf (-7)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 19 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.leaf (-26)))]
  high := ![(.branch 58 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 46 (.leaf (-45)) (.leaf (-44))) (.branch 58 (.leaf (-33)) (.branch 59 (.leaf (-22)) (.leaf (-11))))),
  (.branch 27 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 38 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11))))),
  (.branch 57 (.branch 48 (.leaf (-20)) (.branch 56 (.leaf (-19)) (.leaf (-16)))) (.branch 58 (.leaf (-13)) (.branch 59 (.leaf (-10)) (.leaf (-7))))),
  (.branch 59 (.leaf (-10)) (.leaf (-8))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.leaf (-1)) (.leaf (0))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_299_5412 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (6)) (.leaf (3))) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (7)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (8))) (.branch 29 (.leaf (3)) (.leaf (0))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (5)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (4)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (6))) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (4))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (7)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (0))) (.branch 51 (.leaf (1)) (.leaf (5))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (4)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (8)) (.leaf (3))))))))
  code := certificateP9_5412
  counts := ![(.branch 30 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))) (.branch 44 (.branch 35 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.branch 41 (.leaf (14)) (.leaf (15))))) (.branch 53 (.branch 47 (.leaf (16)) (.branch 50 (.leaf (17)) (.leaf (18)))) (.branch 55 (.leaf (19)) (.branch 58 (.leaf (20)) (.leaf (21))))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 59 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-13)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 43 (.leaf (-13)) (.leaf (-17)))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-22))),
  (.branch 19 (.leaf (0)) (.branch 48 (.leaf (-11)) (.leaf (-12)))),
  (.branch 28 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 56 (.leaf (-15)) (.branch 59 (.leaf (-14)) (.leaf (-7)))),
  (.branch 58 (.branch 52 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.leaf (-1)) (.leaf (0))),
  (.branch 57 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 58 (.leaf (-15)) (.branch 59 (.leaf (-14)) (.leaf (-13))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 43 (.branch 40 (.branch 9 (.leaf (-22)) (.leaf (-21))) (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18))))) (.branch 46 (.branch 44 (.leaf (-17)) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_299_5413 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (3))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (4))) (.branch 14 (.leaf (7)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (2))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (5)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (8))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (1)) (.leaf (6))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (4))) (.branch 44 (.leaf (7)) (.leaf (0)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (5)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (2))) (.branch 51 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (6)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (3)) (.leaf (8))))))))
  code := certificateP9_5413
  counts := ![(.branch 28 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 45 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 52 (.branch 48 (.leaf (14)) (.leaf (15))) (.branch 54 (.leaf (16)) (.branch 58 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.branch 60 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 24 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-12)) (.leaf (-14)))) (.branch 34 (.leaf (-16)) (.branch 54 (.leaf (-17)) (.leaf (-19))))),
  (.branch 25 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 10 (.leaf (-6)) (.branch 21 (.leaf (-8)) (.leaf (-9))))) (.branch 40 (.branch 36 (.leaf (-11)) (.leaf (-12))) (.branch 51 (.leaf (-14)) (.branch 55 (.leaf (-15)) (.leaf (-17)))))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (-13)) (.leaf (-14)))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 14 (.leaf (0)) (.leaf (-16))),
  (.leaf (0))]
  high := ![(.branch 55 (.leaf (-19)) (.branch 59 (.leaf (-16)) (.leaf (-11)))),
  (.branch 57 (.branch 56 (.leaf (-17)) (.leaf (-16))) (.branch 58 (.leaf (-15)) (.branch 59 (.leaf (-14)) (.leaf (-13))))),
  (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1)),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_299_5414 : CycleWitness 9 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (6)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (0))) (.branch 14 (.leaf (7)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (5))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (8)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (1)) (.leaf (0))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (2)) (.branch 32 (.leaf (4)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (3))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 40 (.leaf (5)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (4))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (7)) (.branch 47 (.leaf (0)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (4))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (8))) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_5414
  counts := ![(.branch 30 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 16 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))) (.branch 44 (.branch 36 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.branch 41 (.leaf (14)) (.leaf (15))))) (.branch 53 (.branch 47 (.leaf (16)) (.branch 50 (.leaf (17)) (.leaf (18)))) (.branch 56 (.leaf (19)) (.branch 58 (.leaf (20)) (.leaf (21))))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 59 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-3)) (.branch 51 (.leaf (-4)) (.leaf (-5))))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 34 (.leaf (-25)) (.leaf (-28)))),
  (.branch 14 (.leaf (0)) (.leaf (-17))),
  (.branch 26 (.leaf (0)) (.branch 54 (.leaf (-5)) (.leaf (-8))))]
  high := ![(.branch 59 (.leaf (-14)) (.leaf (-7))),
  (.branch 57 (.branch 56 (.leaf (-15)) (.leaf (-12))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3))))),
  (.branch 52 (.leaf (-5)) (.leaf (-4))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-28)) (.branch 36 (.leaf (-27)) (.leaf (-26)))) (.branch 38 (.leaf (-25)) (.branch 39 (.leaf (-24)) (.leaf (-23))))) (.branch 43 (.branch 41 (.leaf (-22)) (.branch 42 (.leaf (-21)) (.leaf (-20)))) (.branch 45 (.branch 44 (.leaf (-19)) (.leaf (-18))) (.branch 46 (.leaf (-17)) (.leaf (-16)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-15)) (.branch 49 (.leaf (-14)) (.leaf (-13)))) (.branch 51 (.leaf (-12)) (.branch 52 (.leaf (-11)) (.leaf (-10))))) (.branch 56 (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-8)) (.leaf (-7)))) (.branch 58 (.branch 57 (.leaf (-6)) (.leaf (-5))) (.branch 59 (.leaf (-4)) (.leaf (-3))))))),
  (.branch 52 (.branch 48 (.branch 15 (.leaf (-17)) (.branch 47 (.leaf (-16)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-14)) (.leaf (-13))) (.branch 51 (.leaf (-12)) (.leaf (-11))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-10)) (.leaf (-9))) (.branch 55 (.leaf (-8)) (.leaf (-7)))) (.branch 58 (.branch 57 (.leaf (-6)) (.leaf (-5))) (.branch 59 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 57 (.branch 55 (.leaf (-8)) (.branch 56 (.leaf (-7)) (.leaf (-6)))) (.branch 58 (.leaf (-5)) (.branch 59 (.leaf (-4)) (.leaf (-3)))))]
def witnessP9_299 : Fin 50 → CycleWitness 9 := ![witnessP9_299_5365, witnessP9_299_5366, witnessP9_299_5367, witnessP9_299_5368, witnessP9_299_5369, witnessP9_299_5370, witnessP9_299_5371, witnessP9_299_5372, witnessP9_299_5373, witnessP9_299_5374, witnessP9_299_5375, witnessP9_299_5376, witnessP9_299_5377, witnessP9_299_5378, witnessP9_299_5379, witnessP9_299_5380, witnessP9_299_5381, witnessP9_299_5382, witnessP9_299_5383, witnessP9_299_5384, witnessP9_299_5385, witnessP9_299_5386, witnessP9_299_5387, witnessP9_299_5388, witnessP9_299_5389, witnessP9_299_5390, witnessP9_299_5391, witnessP9_299_5392, witnessP9_299_5393, witnessP9_299_5394, witnessP9_299_5395, witnessP9_299_5396, witnessP9_299_5397, witnessP9_299_5398, witnessP9_299_5399, witnessP9_299_5400, witnessP9_299_5401, witnessP9_299_5402, witnessP9_299_5403, witnessP9_299_5404, witnessP9_299_5405, witnessP9_299_5406, witnessP9_299_5407, witnessP9_299_5408, witnessP9_299_5409, witnessP9_299_5410, witnessP9_299_5411, witnessP9_299_5412, witnessP9_299_5413, witnessP9_299_5414]
end RealPinwheel.FiveSixths


