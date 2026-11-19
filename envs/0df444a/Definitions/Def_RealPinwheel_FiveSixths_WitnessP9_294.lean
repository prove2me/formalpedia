-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_294
-- name    : RealPinwheel_FiveSixths_WitnessP9_294
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:20:36.321697+00:00
-- url     : https://prove2.me/theorems/3071198a-de59-449e-afe2-8b1db28748f7
-- title:
--   Exact witness block P9_294
-- statement:
--   These exact witnesses represent words 5124 through 5169 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 5124–5169; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_294_5123 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (7)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (4)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (6)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (5)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (3)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (8)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (5))) (.branch 43 (.leaf (1)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (4)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (5)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (6)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (4))) (.branch 59 (.leaf (1)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_5123
  counts := ![(.branch 29 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 59 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 32 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-20))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-2)) (.leaf (-4)))),
  (.branch 23 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-57))),
  (.branch 39 (.leaf (0)) (.leaf (-25)))]
  high := ![(.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 61 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 48 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.branch 21 (.branch 14 (.branch 10 (.branch 8 (.leaf (-57)) (.branch 9 (.leaf (-56)) (.leaf (-55)))) (.branch 12 (.branch 11 (.leaf (-54)) (.leaf (-53))) (.branch 13 (.leaf (-52)) (.leaf (-51))))) (.branch 17 (.branch 15 (.leaf (-50)) (.branch 16 (.leaf (-49)) (.leaf (-48)))) (.branch 19 (.branch 18 (.leaf (-47)) (.leaf (-46))) (.branch 20 (.leaf (-45)) (.leaf (-44)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-43)) (.branch 23 (.leaf (-42)) (.leaf (-41)))) (.branch 26 (.branch 25 (.leaf (-40)) (.leaf (-39))) (.branch 27 (.leaf (-38)) (.leaf (-37))))) (.branch 31 (.branch 29 (.leaf (-36)) (.branch 30 (.leaf (-35)) (.leaf (-34)))) (.branch 33 (.branch 32 (.leaf (-33)) (.leaf (-32))) (.branch 34 (.leaf (-31)) (.leaf (-30))))))) (.branch 49 (.branch 42 (.branch 38 (.branch 36 (.leaf (-29)) (.branch 37 (.leaf (-28)) (.leaf (-27)))) (.branch 40 (.branch 39 (.leaf (-26)) (.leaf (-25))) (.branch 41 (.leaf (-24)) (.leaf (-23))))) (.branch 45 (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20)))) (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))))) (.branch 56 (.branch 52 (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 51 (.branch 45 (.branch 42 (.branch 40 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-23)))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))) (.branch 48 (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17)))) (.branch 49 (.leaf (-16)) (.branch 50 (.leaf (-15)) (.leaf (-14)))))) (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_294_5124 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (4))) (.branch 15 (.leaf (2)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (6)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (7)) (.leaf (0))) (.branch 23 (.leaf (4)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (1))) (.branch 27 (.leaf (6)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (8)) (.leaf (3))) (.branch 31 (.leaf (2)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (5)) (.leaf (6)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (0))) (.branch 39 (.leaf (3)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (4)) (.leaf (1))) (.branch 43 (.leaf (5)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (8)) (.leaf (6))) (.branch 47 (.leaf (2)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (4)) (.leaf (5)))) (.branch 54 (.branch 53 (.leaf (7)) (.leaf (0))) (.branch 55 (.leaf (6)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (4)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (8)) (.leaf (5))) (.branch 63 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_5124
  counts := ![(.branch 28 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.leaf (7))))),
  (.branch 36 (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 55 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 64 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-31))) (.branch 20 (.leaf (-37)) (.leaf (-38)))),
  (.branch 4 (.leaf (0)) (.branch 59 (.leaf (-26)) (.leaf (-27)))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))) (.branch 43 (.leaf (-13)) (.branch 52 (.leaf (-15)) (.leaf (-16))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (-1))) (.branch 36 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 61 (.branch 55 (.leaf (-14)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 60 (.branch 58 (.branch 21 (.leaf (-38)) (.leaf (-37))) (.branch 59 (.leaf (-32)) (.leaf (-27)))) (.branch 62 (.branch 61 (.leaf (-22)) (.leaf (-17))) (.branch 63 (.leaf (-12)) (.leaf (-7))))),
  (.branch 61 (.branch 60 (.leaf (-27)) (.leaf (-22))) (.branch 62 (.leaf (-17)) (.branch 63 (.leaf (-12)) (.leaf (-7))))),
  (.branch 53 (.leaf (-16)) (.branch 63 (.leaf (-12)) (.leaf (-7)))),
  (.branch 37 (.leaf (-4)) (.branch 56 (.leaf (-1)) (.leaf (0)))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_294_5125 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (8))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (6)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (7)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (4)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (8)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (3)) (.leaf (6)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (4)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (7))) (.branch 43 (.leaf (1)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (5)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (8)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (4)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (6))) (.branch 59 (.leaf (1)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (7)) (.leaf (2))))))))
  code := certificateP9_5125
  counts := ![(.branch 29 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 59 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 32 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-52))),
  (.branch 15 (.leaf (0)) (.branch 36 (.leaf (-19)) (.leaf (-20)))),
  (.branch 20 (.leaf (0)) (.leaf (-4))),
  (.branch 31 (.branch 10 (.leaf (0)) (.leaf (-34))) (.branch 52 (.leaf (-35)) (.leaf (-36))))]
  high := ![(.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 61 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 55 (.branch 50 (.branch 48 (.branch 5 (.leaf (-52)) (.leaf (-51))) (.branch 49 (.leaf (-48)) (.leaf (-45)))) (.branch 52 (.branch 51 (.leaf (-42)) (.leaf (-39))) (.branch 53 (.leaf (-36)) (.branch 54 (.leaf (-33)) (.leaf (-30)))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-27)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 60 (.branch 37 (.leaf (-20)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 58 (.branch 55 (.branch 53 (.leaf (-36)) (.branch 54 (.leaf (-33)) (.leaf (-30)))) (.branch 56 (.leaf (-27)) (.branch 57 (.leaf (-24)) (.leaf (-21))))) (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))))]
def witnessP9_294_5126 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (3))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (5))) (.branch 15 (.leaf (1)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (3)) (.leaf (8)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (4)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (3))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (6)) (.leaf (7))) (.branch 31 (.leaf (2)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (3)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (0))) (.branch 39 (.leaf (4)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (8)) (.leaf (3))) (.branch 43 (.leaf (2)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (6)) (.leaf (5))) (.branch 47 (.leaf (1)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (3)) (.leaf (7)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (5)) (.leaf (3))) (.branch 59 (.leaf (1)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (6)) (.leaf (8))) (.branch 63 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_5126
  counts := ![(.branch 28 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 37 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 27 (.leaf (-24)) (.leaf (-25)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-20)) (.leaf (-22)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (-37)) (.leaf (-38)))),
  (.branch 41 (.branch 20 (.leaf (0)) (.leaf (-4))) (.branch 62 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 61 (.branch 55 (.leaf (-14)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.branch 60 (.leaf (-25)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 44 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-5)))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.leaf (-1)) (.leaf (0))),
  (.branch 60 (.branch 58 (.branch 47 (.leaf (-22)) (.leaf (-21))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 54 (.branch 31 (.leaf (-38)) (.branch 53 (.leaf (-36)) (.leaf (-33)))) (.branch 55 (.leaf (-30)) (.branch 56 (.leaf (-27)) (.leaf (-24))))) (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 63 (.leaf (-6)) (.leaf (-3)))]
def witnessP9_294_5127 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (8)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (4)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (3))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (6)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (1))) (.branch 47 (.leaf (0)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (4)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (3))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (7)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (1))) (.branch 63 (.leaf (0)) (.leaf (3))))))))
  code := certificateP9_5127
  counts := ![(.branch 31 (.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))) (.branch 47 (.branch 39 (.branch 33 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14)))) (.branch 41 (.leaf (15)) (.branch 44 (.leaf (16)) (.leaf (17))))) (.branch 55 (.branch 49 (.leaf (18)) (.branch 52 (.leaf (19)) (.leaf (20)))) (.branch 60 (.branch 57 (.leaf (21)) (.leaf (22))) (.branch 63 (.leaf (23)) (.leaf (24))))))),
  (.branch 30 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 29 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1))),
  (.branch 59 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 11 (.leaf (0)) (.leaf (-53))),
  (.branch 43 (.leaf (0)) (.leaf (-21))),
  (.branch 59 (.leaf (0)) (.leaf (-5))),
  (.branch 27 (.leaf (0)) (.leaf (-37)))]
  high := ![(.branch 58 (.leaf (-5)) (.branch 61 (.leaf (-4)) (.leaf (-3)))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 24 (.branch 17 (.branch 14 (.branch 12 (.leaf (-53)) (.branch 13 (.leaf (-52)) (.leaf (-51)))) (.branch 15 (.leaf (-50)) (.branch 16 (.leaf (-49)) (.leaf (-48))))) (.branch 20 (.branch 18 (.leaf (-47)) (.branch 19 (.leaf (-46)) (.leaf (-45)))) (.branch 22 (.branch 21 (.leaf (-44)) (.leaf (-43))) (.branch 23 (.leaf (-42)) (.leaf (-41)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-40)) (.branch 26 (.leaf (-39)) (.leaf (-38)))) (.branch 28 (.leaf (-37)) (.branch 29 (.leaf (-36)) (.leaf (-35))))) (.branch 33 (.branch 31 (.leaf (-34)) (.branch 32 (.leaf (-33)) (.leaf (-32)))) (.branch 35 (.branch 34 (.leaf (-31)) (.leaf (-30))) (.branch 36 (.leaf (-29)) (.leaf (-28))))))) (.branch 50 (.branch 43 (.branch 40 (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19)))) (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 53 (.branch 48 (.branch 45 (.branch 44 (.leaf (-21)) (.leaf (-20))) (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17))))) (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 36 (.branch 31 (.branch 29 (.branch 28 (.leaf (-37)) (.leaf (-36))) (.branch 30 (.leaf (-35)) (.leaf (-34)))) (.branch 33 (.branch 32 (.leaf (-33)) (.leaf (-32))) (.branch 34 (.leaf (-31)) (.branch 35 (.leaf (-30)) (.leaf (-29)))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 42 (.branch 41 (.leaf (-24)) (.leaf (-23))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))))) (.branch 54 (.branch 49 (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_294_5128 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (8))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (5))) (.branch 23 (.leaf (2)) (.leaf (6))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (8)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (5)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (7))) (.branch 39 (.leaf (0)) (.leaf (6))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (4)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (2))) (.branch 47 (.leaf (0)) (.leaf (5)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (8)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (4))) (.branch 55 (.leaf (2)) (.leaf (6))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (7)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (5)) (.leaf (0))) (.branch 63 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5128
  counts := ![(.branch 30 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 28 (.leaf (9)) (.leaf (10)))))) (.branch 47 (.branch 39 (.branch 33 (.leaf (11)) (.branch 36 (.leaf (12)) (.leaf (13)))) (.branch 43 (.leaf (14)) (.branch 45 (.leaf (15)) (.leaf (16))))) (.branch 57 (.branch 51 (.leaf (17)) (.branch 53 (.leaf (18)) (.leaf (19)))) (.branch 60 (.leaf (20)) (.branch 62 (.leaf (21)) (.leaf (22))))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 12 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 61 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 38 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 47 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.branch 37 (.leaf (-7)) (.leaf (-11)))),
  (.branch 20 (.leaf (0)) (.branch 52 (.leaf (-6)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 41 (.leaf (-49)) (.leaf (-51)))),
  (.branch 9 (.leaf (0)) (.leaf (-19))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 38 (.branch 17 (.leaf (0)) (.leaf (-13))) (.branch 59 (.leaf (-14)) (.leaf (-15)))),
  (.branch 6 (.leaf (0)) (.branch 27 (.leaf (-46)) (.leaf (-47))))]
  high := ![(.branch 63 (.leaf (-4)) (.leaf (-3))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.leaf (-11)) (.leaf (-10))),
  (.branch 55 (.branch 53 (.leaf (-11)) (.branch 54 (.leaf (-9)) (.leaf (-7)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-3))) (.branch 58 (.leaf (-1)) (.leaf (0))))),
  (.branch 58 (.branch 55 (.branch 42 (.leaf (-51)) (.leaf (-50))) (.branch 56 (.leaf (-45)) (.branch 57 (.leaf (-40)) (.leaf (-35))))) (.branch 61 (.branch 59 (.leaf (-30)) (.branch 60 (.leaf (-25)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 36 (.branch 10 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17)))) (.branch 62 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 56 (.branch 52 (.branch 50 (.branch 28 (.leaf (-47)) (.leaf (-45))) (.branch 51 (.leaf (-42)) (.leaf (-39)))) (.branch 54 (.branch 53 (.leaf (-36)) (.leaf (-33))) (.branch 55 (.leaf (-30)) (.leaf (-27))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-24)) (.leaf (-21))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))))]
def witnessP9_294_5129 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (6))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (7)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (8)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (5))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (6))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (4)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (8))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (5)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (4)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (6)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (7))) (.branch 59 (.leaf (0)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_5129
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 40 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 56 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-49)) (.leaf (-50)))),
  (.branch 10 (.leaf (0)) (.leaf (-34))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (-16))) (.branch 58 (.leaf (-17)) (.leaf (-18)))),
  (.branch 21 (.leaf (0)) (.branch 42 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 53 (.leaf (-12)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 55 (.branch 51 (.branch 49 (.branch 27 (.leaf (-50)) (.leaf (-48))) (.branch 50 (.leaf (-45)) (.leaf (-42)))) (.branch 53 (.branch 52 (.leaf (-39)) (.leaf (-36))) (.branch 54 (.leaf (-33)) (.leaf (-30))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-27)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 58 (.branch 55 (.branch 11 (.leaf (-34)) (.branch 54 (.leaf (-33)) (.leaf (-30)))) (.branch 56 (.leaf (-27)) (.branch 57 (.leaf (-24)) (.leaf (-21))))) (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 43 (.leaf (-2)) (.leaf (0)))]
def witnessP9_294_5130 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (2))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (7))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (1))) (.branch 15 (.leaf (3)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (4)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (8))) (.branch 23 (.leaf (3)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (3))) (.branch 31 (.leaf (2)) (.leaf (7))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (4)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (2))) (.branch 39 (.leaf (3)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (8))) (.branch 43 (.leaf (2)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (1))) (.branch 47 (.leaf (3)) (.leaf (5)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (4)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (7))) (.branch 55 (.leaf (3)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (6))) (.branch 59 (.leaf (1)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (4)) (.leaf (3))) (.branch 63 (.leaf (2)) (.leaf (8))))))))
  code := certificateP9_5130
  counts := ![(.branch 28 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 38 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 14 (.leaf (-24)) (.leaf (-26)))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 43 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.branch 30 (.leaf (-1)) (.leaf (-2)))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 35 (.leaf (-8)) (.branch 51 (.leaf (-10)) (.leaf (-12))))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-49)) (.leaf (-50)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (-16))) (.branch 58 (.leaf (-17)) (.leaf (-18)))),
  (.branch 10 (.leaf (0)) (.leaf (-23))),
  (.branch 42 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 61 (.branch 47 (.leaf (-26)) (.branch 60 (.leaf (-25)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 57 (.leaf (-5)) (.leaf (-4))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 62 (.branch 52 (.leaf (-12)) (.leaf (-11))) (.branch 63 (.leaf (-10)) (.leaf (-9)))),
  (.branch 55 (.branch 51 (.branch 49 (.branch 27 (.leaf (-50)) (.leaf (-48))) (.branch 50 (.leaf (-45)) (.leaf (-42)))) (.branch 53 (.branch 52 (.leaf (-39)) (.leaf (-36))) (.branch 54 (.leaf (-33)) (.leaf (-30))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-27)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 58 (.branch 55 (.branch 11 (.leaf (-23)) (.branch 33 (.leaf (-22)) (.leaf (-21)))) (.branch 56 (.leaf (-19)) (.branch 57 (.leaf (-17)) (.leaf (-15))))) (.branch 61 (.branch 59 (.leaf (-13)) (.branch 60 (.leaf (-11)) (.leaf (-9)))) (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 43 (.leaf (-2)) (.leaf (0)))]
def witnessP9_294_5131 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (6))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (8)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (6))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (0))) (.branch 27 (.leaf (7)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (6)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (4)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (8)) (.leaf (5))) (.branch 39 (.leaf (0)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (3)) (.leaf (6)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (0))) (.branch 47 (.leaf (1)) (.leaf (7)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (3)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (4))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (6)) (.leaf (0))) (.branch 59 (.leaf (8)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (0))) (.branch 63 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_5131
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 38 (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.branch 10 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.leaf (-22))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (-8)) (.leaf (-9)))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-23)) (.leaf (-25)))),
  (.branch 12 (.leaf (0)) (.branch 50 (.leaf (-4)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-34)) (.leaf (-38)))),
  (.branch 5 (.leaf (0)) (.leaf (-49))),
  (.branch 16 (.leaf (0)) (.branch 37 (.leaf (-16)) (.leaf (-17))))]
  high := ![(.branch 59 (.leaf (-14)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 61 (.branch 35 (.leaf (-22)) (.branch 48 (.leaf (-21)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 54 (.leaf (-1)) (.leaf (0))),
  (.branch 59 (.branch 57 (.branch 46 (.leaf (-25)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 51 (.leaf (-6)) (.leaf (-5))),
  (.branch 59 (.branch 32 (.branch 19 (.leaf (-38)) (.leaf (-37))) (.branch 45 (.leaf (-36)) (.branch 58 (.leaf (-35)) (.leaf (-30))))) (.branch 61 (.branch 60 (.leaf (-25)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 55 (.branch 51 (.branch 49 (.branch 6 (.leaf (-49)) (.leaf (-48))) (.branch 50 (.leaf (-45)) (.leaf (-42)))) (.branch 53 (.branch 52 (.leaf (-39)) (.leaf (-36))) (.branch 54 (.leaf (-33)) (.leaf (-30))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-27)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 61 (.branch 38 (.leaf (-17)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_294_5132 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (7))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (5))) (.branch 11 (.leaf (8)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (4))) (.branch 15 (.leaf (1)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (7))) (.branch 19 (.leaf (3)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (8)) (.leaf (6))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (3))) (.branch 31 (.leaf (7)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (4)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (8))) (.branch 39 (.leaf (0)) (.leaf (3))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (5))) (.branch 43 (.leaf (7)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (4))) (.branch 47 (.leaf (1)) (.leaf (6)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (8))) (.branch 51 (.leaf (3)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (4))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (7)) (.leaf (6))) (.branch 59 (.leaf (1)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (3))) (.branch 63 (.leaf (8)) (.leaf (5))))))))
  code := certificateP9_5132
  counts := ![(.branch 28 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 27 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 59 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (-23)) (.leaf (-24)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-17)) (.leaf (-18)))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (-7))) (.branch 43 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 61 (.branch 50 (.leaf (-13)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.branch 60 (.leaf (-12)) (.leaf (-10))) (.branch 62 (.leaf (-8)) (.branch 63 (.leaf (-6)) (.leaf (-4))))),
  (.branch 62 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-24)) (.leaf (-21))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 43 (.leaf (-2)) (.branch 54 (.leaf (-1)) (.leaf (0)))),
  (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 60 (.branch 58 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 59 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.branch 61 (.leaf (-5)) (.leaf (-4))) (.branch 63 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-2))]
def witnessP9_294_5133 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (7)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (6))) (.branch 11 (.leaf (3)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (8))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (4)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (6))) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (7)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (4)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (0))) (.branch 39 (.leaf (8)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (6))) (.branch 43 (.leaf (3)) (.leaf (2)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (0))) (.branch 47 (.leaf (1)) (.leaf (5)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (7))) (.branch 51 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (6))) (.branch 59 (.leaf (1)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (8)) (.leaf (0))) (.branch 63 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_5133
  counts := ![(.branch 30 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 27 (.leaf (-24)) (.leaf (-25)))),
  (.branch 24 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 56 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 23 (.leaf (-9)) (.branch 55 (.leaf (-10)) (.leaf (-11))))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-43))),
  (.branch 18 (.leaf (0)) (.branch 39 (.leaf (-10)) (.leaf (-11))))]
  high := ![(.branch 58 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 61 (.branch 60 (.leaf (-25)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 57 (.leaf (-5)) (.leaf (-4))),
  (.branch 61 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8)))) (.branch 61 (.branch 60 (.leaf (-7)) (.leaf (-6))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3)))))),
  (.leaf (0)),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 52 (.branch 8 (.leaf (-43)) (.branch 51 (.leaf (-42)) (.leaf (-39)))) (.branch 54 (.branch 53 (.leaf (-36)) (.leaf (-33))) (.branch 55 (.leaf (-30)) (.leaf (-27))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-24)) (.leaf (-21))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 62 (.branch 40 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))]
def witnessP9_294_5134 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (3))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (7)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (3)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (4)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (1)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (4))) (.branch 43 (.leaf (0)) (.leaf (6)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (3)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (4)) (.leaf (5)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (3))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (2)) (.leaf (4))) (.branch 59 (.leaf (0)) (.leaf (8)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (3)) (.leaf (2))))))))
  code := certificateP9_5134
  counts := ![(.branch 30 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 40 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 56 (.branch 49 (.leaf (15)) (.branch 53 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 16 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 60 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-20))),
  (.branch 28 (.leaf (0)) (.leaf (-36))),
  (.branch 60 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 50 (.leaf (-11)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.branch 49 (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16))))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 37 (.branch 32 (.branch 30 (.branch 29 (.leaf (-36)) (.leaf (-35))) (.branch 31 (.leaf (-34)) (.leaf (-33)))) (.branch 34 (.branch 33 (.leaf (-32)) (.leaf (-31))) (.branch 35 (.leaf (-30)) (.branch 36 (.leaf (-29)) (.leaf (-28)))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-27)) (.leaf (-26))) (.branch 40 (.leaf (-25)) (.leaf (-24)))) (.branch 43 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))))) (.branch 55 (.branch 50 (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 52 (.branch 51 (.leaf (-14)) (.leaf (-13))) (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_294_5135 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (7)) (.leaf (3))) (.branch 15 (.leaf (5)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (2)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (8)) (.leaf (1))) (.branch 31 (.leaf (6)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (3)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (4)) (.leaf (6))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (3))) (.branch 43 (.leaf (0)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (7)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (1)) (.leaf (6)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (5))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (4)))) (.branch 62 (.branch 61 (.leaf (8)) (.leaf (2))) (.branch 63 (.leaf (6)) (.leaf (3))))))))
  code := certificateP9_5135
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 37 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 58 (.leaf (8)) (.leaf (9)))))),
  (.branch 34 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 41 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 60 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 29 (.leaf (0)) (.branch 61 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.leaf (-15)))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-46))) (.branch 16 (.leaf (-47)) (.branch 23 (.leaf (-48)) (.leaf (-49))))) (.branch 44 (.branch 37 (.leaf (-50)) (.leaf (-51))) (.branch 51 (.leaf (-52)) (.branch 58 (.leaf (-53)) (.leaf (-54)))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-19))) (.branch 19 (.leaf (-20)) (.branch 26 (.leaf (-21)) (.leaf (-22))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))) (.branch 35 (.branch 28 (.leaf (-3)) (.leaf (-4))) (.branch 42 (.leaf (-5)) (.leaf (-6))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-37)) (.leaf (-38)))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 56 (.leaf (-9)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.branch 40 (.leaf (-3)) (.leaf (-4)))),
  (.branch 13 (.leaf (0)) (.leaf (-19))),
  (.branch 29 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.branch 59 (.leaf (-54)) (.branch 60 (.leaf (-45)) (.leaf (-36)))) (.branch 62 (.leaf (-27)) (.branch 63 (.leaf (-18)) (.leaf (-9))))),
  (.branch 27 (.leaf (-22)) (.branch 63 (.leaf (-18)) (.leaf (-9)))),
  (.branch 43 (.leaf (-6)) (.leaf (0))),
  (.branch 61 (.branch 11 (.leaf (-38)) (.leaf (-36))) (.branch 62 (.leaf (-27)) (.branch 63 (.leaf (-18)) (.leaf (-9))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-10)) (.leaf (-9))) (.branch 59 (.leaf (-8)) (.leaf (-7)))) (.branch 62 (.branch 61 (.leaf (-6)) (.leaf (-5))) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 41 (.leaf (-4)) (.leaf (-3))),
  (.branch 54 (.branch 49 (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_294_5136 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (7)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (3))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (6))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (8))) (.branch 19 (.leaf (2)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (2)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (3))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (7)) (.leaf (5))) (.branch 31 (.leaf (2)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (4)) (.leaf (6)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (0))) (.branch 39 (.leaf (8)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (5)) (.leaf (3))) (.branch 43 (.leaf (2)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (6))) (.branch 47 (.leaf (1)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (7))) (.branch 51 (.leaf (2)) (.leaf (5)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (4))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (6)) (.leaf (3))) (.branch 59 (.leaf (1)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (8)) (.leaf (5))) (.branch 63 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5136
  counts := ![(.branch 28 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 37 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 16 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 27 (.leaf (-24)) (.leaf (-25)))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-2)) (.leaf (-3)))) (.branch 43 (.leaf (-5)) (.branch 55 (.leaf (-6)) (.leaf (-8))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (-2))) (.branch 48 (.leaf (-4)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-23)) (.leaf (-25)))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-20)) (.leaf (-22)))),
  (.branch 7 (.leaf (0)) (.leaf (-43))),
  (.branch 18 (.leaf (0)) (.branch 39 (.leaf (-10)) (.leaf (-11))))]
  high := ![(.branch 61 (.branch 55 (.leaf (-14)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.branch 60 (.leaf (-25)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 56 (.leaf (-8)) (.leaf (-7))),
  (.branch 60 (.branch 49 (.leaf (-6)) (.branch 59 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.branch 61 (.leaf (-3)) (.leaf (-2))) (.branch 63 (.leaf (-1)) (.leaf (0))))),
  (.branch 59 (.branch 57 (.branch 46 (.leaf (-25)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 63 (.leaf (-6)) (.leaf (-3))),
  (.branch 60 (.branch 58 (.branch 47 (.leaf (-22)) (.leaf (-21))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 56 (.branch 52 (.branch 8 (.leaf (-43)) (.branch 51 (.leaf (-42)) (.leaf (-39)))) (.branch 54 (.branch 53 (.leaf (-36)) (.leaf (-33))) (.branch 55 (.leaf (-30)) (.leaf (-27))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-24)) (.leaf (-21))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 62 (.branch 40 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))]
def witnessP9_294_5137 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (3))) (.branch 15 (.leaf (8)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (2)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (7))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (6)) (.leaf (1))) (.branch 31 (.leaf (5)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (3)) (.leaf (8)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (3))) (.branch 43 (.leaf (0)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (6)) (.leaf (4))) (.branch 47 (.leaf (7)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (1)) (.leaf (5)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (8))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (4)))) (.branch 62 (.branch 61 (.leaf (6)) (.leaf (2))) (.branch 63 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_5137
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 37 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 58 (.leaf (8)) (.leaf (9)))))),
  (.branch 34 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 41 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 60 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.leaf (-15)))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-46))) (.branch 16 (.leaf (-47)) (.branch 23 (.leaf (-48)) (.leaf (-49))))) (.branch 44 (.branch 37 (.leaf (-50)) (.leaf (-51))) (.branch 51 (.leaf (-52)) (.branch 58 (.leaf (-53)) (.leaf (-54)))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-19))) (.branch 19 (.leaf (-20)) (.branch 26 (.leaf (-21)) (.leaf (-22))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))) (.branch 35 (.branch 28 (.leaf (-3)) (.leaf (-4))) (.branch 42 (.leaf (-5)) (.leaf (-6))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-37)) (.leaf (-38)))),
  (.branch 8 (.leaf (0)) (.branch 40 (.leaf (-3)) (.leaf (-4)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (-18)) (.leaf (-20)))),
  (.branch 36 (.branch 15 (.leaf (0)) (.leaf (-7))) (.branch 56 (.leaf (-8)) (.leaf (-10))))]
  high := ![(.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.branch 59 (.leaf (-54)) (.branch 60 (.leaf (-45)) (.leaf (-36)))) (.branch 62 (.leaf (-27)) (.branch 63 (.leaf (-18)) (.leaf (-9))))),
  (.branch 27 (.leaf (-22)) (.branch 63 (.leaf (-18)) (.leaf (-9)))),
  (.branch 43 (.leaf (-6)) (.leaf (0))),
  (.branch 61 (.branch 11 (.leaf (-38)) (.leaf (-36))) (.branch 62 (.leaf (-27)) (.branch 63 (.leaf (-18)) (.leaf (-9))))),
  (.branch 41 (.leaf (-4)) (.leaf (-3))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.branch 50 (.branch 48 (.branch 25 (.leaf (-20)) (.leaf (-19))) (.branch 49 (.leaf (-18)) (.leaf (-17)))) (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8)))) (.branch 61 (.branch 60 (.leaf (-7)) (.leaf (-6))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-10)) (.leaf (-9))) (.branch 59 (.leaf (-8)) (.leaf (-7)))) (.branch 62 (.branch 61 (.leaf (-6)) (.leaf (-5))) (.branch 63 (.leaf (-4)) (.leaf (-3)))))]
def witnessP9_294_5138 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (4))) (.branch 11 (.leaf (6)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (5))) (.branch 15 (.leaf (2)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (8)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (2))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (3))) (.branch 27 (.leaf (6)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (7))) (.branch 31 (.leaf (2)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (5)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (2))) (.branch 39 (.leaf (1)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (8)) (.leaf (4))) (.branch 43 (.leaf (6)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (5))) (.branch 47 (.leaf (2)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (7)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (2))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (5)) (.leaf (3))) (.branch 59 (.leaf (6)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (8))) (.branch 63 (.leaf (2)) (.leaf (4))))))))
  code := certificateP9_5138
  counts := ![(.branch 29 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 36 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-17)) (.leaf (-18)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 30 (.branch 9 (.leaf (0)) (.leaf (-37))) (.branch 51 (.leaf (-38)) (.leaf (-39)))),
  (.branch 19 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 62 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 43 (.leaf (-2)) (.branch 54 (.leaf (-1)) (.leaf (0)))),
  (.branch 59 (.branch 47 (.branch 36 (.leaf (-23)) (.leaf (-22))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 57 (.branch 54 (.branch 52 (.leaf (-39)) (.branch 53 (.leaf (-36)) (.leaf (-33)))) (.branch 55 (.leaf (-30)) (.branch 56 (.leaf (-27)) (.leaf (-24))))) (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 20 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3))))]
def witnessP9_294_5139 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (7))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (6))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (8))) (.branch 15 (.leaf (1)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (3))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (7))) (.branch 23 (.leaf (6)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (8))) (.branch 31 (.leaf (3)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (6)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (7))) (.branch 39 (.leaf (2)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (5))) (.branch 43 (.leaf (3)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (8))) (.branch 47 (.leaf (1)) (.leaf (6)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (4))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (7))) (.branch 55 (.leaf (5)) (.leaf (3))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (1)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (6)) (.leaf (8))) (.branch 63 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_5139
  counts := ![(.branch 28 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 39 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 61 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 27 (.leaf (-24)) (.leaf (-25)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 43 (.leaf (-39)) (.leaf (-41)))),
  (.branch 11 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.leaf (-49))),
  (.branch 10 (.leaf (0)) (.branch 35 (.leaf (-14)) (.leaf (-17)))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 61 (.branch 60 (.leaf (-25)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 52 (.leaf (-1)) (.leaf (0))),
  (.branch 59 (.branch 57 (.branch 44 (.leaf (-41)) (.leaf (-40))) (.branch 58 (.leaf (-35)) (.leaf (-30)))) (.branch 61 (.branch 60 (.leaf (-25)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 25 (.branch 12 (.leaf (-9)) (.leaf (-8))) (.branch 38 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5))))),
  (.branch 57 (.branch 30 (.branch 4 (.leaf (-49)) (.branch 17 (.leaf (-48)) (.leaf (-47)))) (.branch 43 (.leaf (-46)) (.branch 56 (.leaf (-45)) (.leaf (-40))))) (.branch 60 (.branch 58 (.leaf (-35)) (.branch 59 (.leaf (-30)) (.leaf (-25)))) (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 49 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_294_5140 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (8)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (7)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (5)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (8))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (3)) (.leaf (6)))) (.branch 46 (.branch 45 (.leaf (5)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (7)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (3)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (5))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (4)) (.leaf (6)))) (.branch 62 (.branch 61 (.leaf (8)) (.leaf (0))) (.branch 63 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5140
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.branch 10 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-23)) (.leaf (-25)))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (-40)) (.leaf (-41)))),
  (.branch 40 (.branch 19 (.leaf (0)) (.leaf (-7))) (.branch 61 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 59 (.leaf (-14)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 54 (.leaf (-1)) (.leaf (0))),
  (.branch 60 (.branch 38 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 59 (.branch 57 (.branch 46 (.leaf (-25)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 53 (.branch 30 (.leaf (-41)) (.branch 52 (.leaf (-39)) (.leaf (-36)))) (.branch 55 (.branch 54 (.leaf (-33)) (.leaf (-30))) (.branch 56 (.leaf (-27)) (.leaf (-24))))) (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))]
def witnessP9_294_5141 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (8)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (7)) (.leaf (1))) (.branch 31 (.leaf (4)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (6)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (1)) (.leaf (8))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (2))) (.branch 43 (.leaf (3)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (5)) (.leaf (0))) (.branch 47 (.leaf (4)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (7)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (6))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (2))) (.branch 59 (.leaf (3)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (8)) (.leaf (1))) (.branch 63 (.leaf (4)) (.leaf (2))))))))
  code := certificateP9_5141
  counts := ![(.branch 28 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 41 (.leaf (9)) (.leaf (10)))) (.branch 55 (.branch 50 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 30 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 39 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 57 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 32 (.branch 16 (.branch 6 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 38 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-11)) (.leaf (-13)))) (.branch 41 (.branch 18 (.leaf (-15)) (.leaf (-16))) (.branch 50 (.leaf (-17)) (.leaf (-18))))),
  (.branch 25 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 34 (.leaf (-9)) (.branch 57 (.leaf (-10)) (.leaf (-11))))),
  (.branch 26 (.branch 10 (.leaf (0)) (.leaf (-2))) (.branch 42 (.leaf (-3)) (.branch 58 (.leaf (-4)) (.leaf (-5))))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 24 (.branch 3 (.leaf (0)) (.leaf (-55))) (.branch 45 (.leaf (-56)) (.leaf (-57)))),
  (.branch 13 (.leaf (0)) (.leaf (-25))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (-40)) (.leaf (-41)))),
  (.branch 40 (.branch 19 (.leaf (0)) (.leaf (-7))) (.branch 61 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 61 (.branch 51 (.leaf (-18)) (.branch 56 (.leaf (-17)) (.leaf (-16)))) (.branch 62 (.leaf (-13)) (.branch 63 (.leaf (-10)) (.leaf (-7))))),
  (.branch 58 (.leaf (-11)) (.branch 63 (.leaf (-10)) (.leaf (-7)))),
  (.branch 60 (.branch 59 (.leaf (-5)) (.leaf (-3))) (.branch 61 (.leaf (-1)) (.leaf (0)))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 54 (.branch 49 (.branch 47 (.branch 46 (.leaf (-57)) (.leaf (-54))) (.branch 48 (.leaf (-51)) (.leaf (-48)))) (.branch 51 (.branch 50 (.leaf (-45)) (.leaf (-42))) (.branch 52 (.leaf (-39)) (.branch 53 (.leaf (-36)) (.leaf (-33)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-30)) (.leaf (-27))) (.branch 57 (.leaf (-24)) (.branch 58 (.leaf (-21)) (.leaf (-18))))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 59 (.branch 57 (.branch 14 (.leaf (-25)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 57 (.branch 53 (.branch 30 (.leaf (-41)) (.branch 52 (.leaf (-39)) (.leaf (-36)))) (.branch 55 (.branch 54 (.leaf (-33)) (.leaf (-30))) (.branch 56 (.leaf (-27)) (.leaf (-24))))) (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))]
def witnessP9_294_5142 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (8)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (3)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (7)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (0))) (.branch 23 (.leaf (2)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (8)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (2))) (.branch 31 (.leaf (4)) (.leaf (7))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (6)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (8)) (.leaf (0))) (.branch 39 (.leaf (2)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (5)) (.leaf (4))) (.branch 43 (.leaf (0)) (.leaf (7)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (2))) (.branch 47 (.leaf (3)) (.leaf (6)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (8)) (.leaf (4)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (7)) (.leaf (3))) (.branch 59 (.leaf (0)) (.leaf (6)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (2))) (.branch 63 (.leaf (4)) (.leaf (8))))))))
  code := certificateP9_5142
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-20))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-2)) (.leaf (-4)))),
  (.branch 28 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 53 (.leaf (-11)) (.leaf (-12)))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.branch 37 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 62 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 60 (.branch 48 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-12)) (.leaf (-11))) (.branch 56 (.leaf (-10)) (.branch 57 (.leaf (-9)) (.leaf (-8))))) (.branch 61 (.branch 59 (.leaf (-7)) (.branch 60 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.leaf (-4)) (.branch 63 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 62 (.branch 61 (.leaf (-5)) (.leaf (-4))) (.branch 63 (.leaf (-3)) (.leaf (-2)))),
  (.branch 60 (.branch 58 (.leaf (-8)) (.branch 59 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.branch 61 (.leaf (-5)) (.leaf (-4))) (.branch 63 (.leaf (-3)) (.leaf (-2))))),
  (.branch 38 (.leaf (-2)) (.branch 52 (.leaf (-1)) (.leaf (0))))]
def witnessP9_294_5143 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (8))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (5))) (.branch 15 (.leaf (7)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (6)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (8)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (7))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (6))) (.branch 31 (.leaf (8)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (5)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (6))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (3)) (.leaf (8))) (.branch 43 (.leaf (2)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (7)) (.leaf (1)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (6)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (8)) (.leaf (4))) (.branch 55 (.leaf (0)) (.leaf (5))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (7))) (.branch 59 (.leaf (3)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (6))) (.branch 63 (.leaf (8)) (.leaf (4))))))))
  code := certificateP9_5143
  counts := ![(.branch 28 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.leaf (7))))),
  (.branch 34 (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 36 (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 64 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-50)) (.leaf (-51)))) (.branch 29 (.leaf (-52)) (.branch 38 (.leaf (-53)) (.leaf (-54))))),
  (.branch 6 (.leaf (0)) (.leaf (-22))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-36))) (.branch 22 (.leaf (-37)) (.leaf (-38)))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))) (.branch 45 (.branch 36 (.leaf (-3)) (.leaf (-4))) (.branch 54 (.leaf (-5)) (.leaf (-6))))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (-23)) (.leaf (-24)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-17)) (.leaf (-19)))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 61 (.branch 50 (.leaf (-13)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 60 (.branch 58 (.branch 39 (.leaf (-54)) (.leaf (-49))) (.branch 59 (.leaf (-42)) (.leaf (-35)))) (.branch 62 (.branch 61 (.leaf (-28)) (.leaf (-21))) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 62 (.branch 7 (.leaf (-22)) (.leaf (-21))) (.branch 63 (.leaf (-14)) (.leaf (-7)))),
  (.branch 61 (.branch 23 (.leaf (-38)) (.branch 60 (.leaf (-35)) (.leaf (-28)))) (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 55 (.leaf (-6)) (.leaf (0))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-24)) (.leaf (-21))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 52 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 60 (.branch 48 (.leaf (-19)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3))]
def witnessP9_294_5144 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (6)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (7)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (4))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (6)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (4))) (.branch 39 (.leaf (2)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (5)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (5)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (8)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (4))) (.branch 55 (.leaf (2)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (5)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (4)) (.leaf (0))) (.branch 63 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_5144
  counts := ![(.branch 30 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 40 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 56 (.branch 49 (.leaf (15)) (.branch 53 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 16 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 3 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 51 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-29))),
  (.branch 19 (.leaf (0)) (.leaf (-45))),
  (.branch 51 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 50 (.leaf (-11)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 49 (.branch 42 (.branch 38 (.branch 36 (.leaf (-29)) (.branch 37 (.leaf (-28)) (.leaf (-27)))) (.branch 40 (.branch 39 (.leaf (-26)) (.leaf (-25))) (.branch 41 (.leaf (-24)) (.leaf (-23))))) (.branch 45 (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20)))) (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))))) (.branch 56 (.branch 52 (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 41 (.branch 30 (.branch 24 (.branch 21 (.branch 20 (.leaf (-45)) (.leaf (-44))) (.branch 22 (.leaf (-43)) (.branch 23 (.leaf (-42)) (.leaf (-41))))) (.branch 27 (.branch 25 (.leaf (-40)) (.branch 26 (.leaf (-39)) (.leaf (-38)))) (.branch 28 (.leaf (-37)) (.branch 29 (.leaf (-36)) (.leaf (-35)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-34)) (.leaf (-33))) (.branch 33 (.leaf (-32)) (.branch 34 (.leaf (-31)) (.leaf (-30))))) (.branch 38 (.branch 36 (.leaf (-29)) (.branch 37 (.leaf (-28)) (.leaf (-27)))) (.branch 39 (.leaf (-26)) (.branch 40 (.leaf (-25)) (.leaf (-24))))))) (.branch 52 (.branch 46 (.branch 43 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))))) (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_294_5145 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (6)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (8)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (6)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (1))) (.branch 19 (.leaf (5)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (4))) (.branch 23 (.leaf (8)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (7)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (6)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (8)) (.leaf (4))) (.branch 39 (.leaf (0)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (5)) (.leaf (1))) (.branch 43 (.leaf (7)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (0))) (.branch 47 (.leaf (6)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (8)) (.leaf (1))) (.branch 51 (.leaf (5)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (4))) (.branch 55 (.leaf (7)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (6)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (8)) (.leaf (2))))))))
  code := certificateP9_5145
  counts := ![(.branch 27 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 33 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 39 (.leaf (-12)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 35 (.leaf (-8)) (.leaf (-9)))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (-8))) (.branch 55 (.leaf (-9)) (.leaf (-10)))),
  (.branch 11 (.leaf (0)) (.branch 23 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 61 (.branch 40 (.leaf (-13)) (.branch 60 (.leaf (-12)) (.leaf (-10)))) (.branch 62 (.leaf (-8)) (.branch 63 (.leaf (-6)) (.leaf (-4))))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 60 (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7)))) (.branch 62 (.branch 61 (.leaf (-6)) (.leaf (-5))) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-9))) (.branch 58 (.leaf (-8)) (.leaf (-7)))) (.branch 61 (.branch 60 (.leaf (-6)) (.leaf (-5))) (.branch 62 (.leaf (-4)) (.branch 63 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 50 (.leaf (-3)) (.leaf (-2)))]
def witnessP9_294_5146 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (7)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (2)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (0))) (.branch 15 (.leaf (6)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (3)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (5))) (.branch 23 (.leaf (0)) (.leaf (7))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (4))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (1))) (.branch 31 (.leaf (6)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (8)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (4))) (.branch 39 (.leaf (1)) (.leaf (3))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (5))) (.branch 43 (.leaf (2)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (7)) (.leaf (0))) (.branch 47 (.leaf (6)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (5))) (.branch 55 (.leaf (0)) (.leaf (8))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (4))) (.branch 59 (.leaf (2)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (3)) (.leaf (1))) (.branch 63 (.leaf (6)) (.leaf (5))))))))
  code := certificateP9_5146
  counts := ![(.branch 28 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 41 (.leaf (9)) (.leaf (10)))) (.branch 55 (.branch 50 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 30 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 39 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 57 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-11)) (.leaf (-13)))) (.branch 41 (.branch 18 (.leaf (-15)) (.leaf (-16))) (.branch 50 (.leaf (-17)) (.leaf (-18))))),
  (.branch 25 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 34 (.leaf (-9)) (.branch 57 (.leaf (-10)) (.leaf (-11))))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (-8)) (.leaf (-9)))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (-5))) (.branch 26 (.leaf (-6)) (.branch 58 (.leaf (-7)) (.leaf (-8))))),
  (.branch 10 (.leaf (0)) (.branch 42 (.leaf (-1)) (.leaf (-2)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 24 (.branch 3 (.leaf (0)) (.leaf (-55))) (.branch 45 (.leaf (-56)) (.leaf (-57)))),
  (.branch 13 (.leaf (0)) (.leaf (-25)))]
  high := ![(.branch 61 (.branch 51 (.leaf (-18)) (.branch 56 (.leaf (-17)) (.leaf (-16)))) (.branch 62 (.leaf (-13)) (.branch 63 (.leaf (-10)) (.leaf (-7))))),
  (.branch 58 (.leaf (-11)) (.branch 63 (.leaf (-10)) (.leaf (-7)))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 59 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 43 (.leaf (-2)) (.branch 55 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 54 (.branch 49 (.branch 47 (.branch 46 (.leaf (-57)) (.leaf (-54))) (.branch 48 (.leaf (-51)) (.leaf (-48)))) (.branch 51 (.branch 50 (.leaf (-45)) (.leaf (-42))) (.branch 52 (.leaf (-39)) (.branch 53 (.leaf (-36)) (.leaf (-33)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-30)) (.leaf (-27))) (.branch 57 (.leaf (-24)) (.branch 58 (.leaf (-21)) (.leaf (-18))))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 59 (.branch 57 (.branch 14 (.leaf (-25)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))))]
def witnessP9_294_5147 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (8)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (7))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (5))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (8)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (7))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (6)) (.leaf (3))) (.branch 31 (.leaf (2)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (8)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (0))) (.branch 39 (.leaf (5)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (3)) (.leaf (7))) (.branch 43 (.leaf (2)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (6)) (.leaf (4))) (.branch 47 (.leaf (1)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (8)) (.leaf (5)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (4)) (.leaf (7))) (.branch 59 (.leaf (1)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (6)) (.leaf (3))) (.branch 63 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_5147
  counts := ![(.branch 28 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 37 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 36 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 14 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 27 (.leaf (-24)) (.leaf (-25)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-9)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 41 (.leaf (-13)) (.leaf (-17)))),
  (.branch 32 (.branch 7 (.leaf (0)) (.leaf (-6))) (.branch 57 (.leaf (-7)) (.leaf (-8)))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 61 (.branch 55 (.leaf (-14)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.branch 60 (.leaf (-25)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 44 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-5)))),
  (.branch 49 (.branch 42 (.leaf (-17)) (.leaf (-16))) (.branch 56 (.leaf (-15)) (.branch 63 (.leaf (-14)) (.leaf (-11))))),
  (.branch 60 (.branch 58 (.leaf (-8)) (.branch 59 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.branch 61 (.leaf (-5)) (.leaf (-4))) (.branch 63 (.leaf (-3)) (.leaf (-2))))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_294_5148 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (8)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (5)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (7)) (.leaf (6))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (0)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (5)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (8)) (.leaf (2))) (.branch 43 (.leaf (0)) (.leaf (4)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (3)) (.leaf (6)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (7)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (5)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (2))) (.branch 59 (.leaf (0)) (.leaf (4)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (8)) (.leaf (6))))))))
  code := certificateP9_5148
  counts := ![(.branch 30 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 24 (.leaf (9)) (.branch 27 (.leaf (10)) (.leaf (11)))))) (.branch 46 (.branch 38 (.branch 33 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14)))) (.branch 40 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17))))) (.branch 54 (.branch 49 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20)))) (.branch 59 (.branch 56 (.leaf (21)) (.leaf (22))) (.branch 62 (.leaf (23)) (.leaf (24))))))),
  (.branch 29 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (-20)) (.leaf (-21)))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-37))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 60 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 57 (.branch 54 (.branch 10 (.leaf (-37)) (.branch 53 (.leaf (-36)) (.leaf (-33)))) (.branch 55 (.leaf (-30)) (.branch 56 (.leaf (-27)) (.leaf (-24))))) (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 42 (.leaf (-5)) (.leaf (-3)))]
def witnessP9_294_5149 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (7)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (8)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (6))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (5)) (.leaf (7))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (1)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (6))) (.branch 39 (.leaf (1)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (4)) (.leaf (0))) (.branch 43 (.leaf (8)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (0))) (.branch 47 (.leaf (5)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (7)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (6))) (.branch 55 (.leaf (0)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (4)) (.leaf (1))) (.branch 59 (.leaf (3)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (1))) (.branch 63 (.leaf (5)) (.leaf (8))))))))
  code := certificateP9_5149
  counts := ![(.branch 28 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 55 (.branch 51 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 30 (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 39 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 43 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 14 (.leaf (-29)) (.branch 23 (.leaf (-30)) (.leaf (-31))))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 4 (.leaf (0)) (.branch 36 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 32 (.branch 11 (.leaf (0)) (.leaf (-11))) (.branch 52 (.leaf (-12)) (.leaf (-14)))),
  (.branch 20 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 61 (.branch 56 (.leaf (-31)) (.leaf (-28))) (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 40 (.leaf (-15)) (.branch 63 (.leaf (-14)) (.leaf (-7)))),
  (.branch 62 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 37 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 61 (.branch 59 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 21 (.leaf (-2)) (.branch 44 (.leaf (-1)) (.leaf (0))))]
def witnessP9_294_5150 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (7))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (8))) (.branch 31 (.leaf (1)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (1)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (0))) (.branch 39 (.leaf (2)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (6)) (.leaf (0))) (.branch 43 (.leaf (3)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (7))) (.branch 47 (.leaf (0)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (4)) (.leaf (1))) (.branch 59 (.leaf (3)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (8))) (.branch 63 (.leaf (1)) (.leaf (6))))))))
  code := certificateP9_5150
  counts := ![(.branch 28 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 56 (.branch 51 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.branch 62 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 19 (.leaf (-26)) (.branch 28 (.leaf (-27)) (.leaf (-28))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (-6))) (.branch 57 (.leaf (-8)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 21 (.leaf (0)) (.branch 41 (.leaf (-1)) (.leaf (-3)))),
  (.branch 14 (.leaf (0)) (.leaf (-18))),
  (.branch 30 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 62 (.branch 61 (.leaf (-28)) (.leaf (-21))) (.branch 63 (.leaf (-14)) (.leaf (-7)))),
  (.branch 45 (.leaf (-12)) (.branch 59 (.leaf (-10)) (.leaf (-7)))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7)))) (.branch 62 (.branch 61 (.leaf (-6)) (.leaf (-5))) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 61 (.branch 59 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 43 (.branch 42 (.leaf (-3)) (.leaf (-2))) (.branch 44 (.leaf (-1)) (.leaf (0)))),
  (.branch 55 (.branch 50 (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 52 (.branch 51 (.leaf (-14)) (.leaf (-13))) (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_294_5151 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (7)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (6))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (8)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (1)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (0))) (.branch 23 (.leaf (7)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (6))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (1))) (.branch 31 (.leaf (4)) (.leaf (8))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (1)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (5)) (.leaf (0))) (.branch 39 (.leaf (7)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (6))) (.branch 43 (.leaf (0)) (.leaf (4)))) (.branch 46 (.branch 45 (.leaf (3)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (8)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (1)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (0))) (.branch 55 (.leaf (7)) (.leaf (4))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (6))) (.branch 59 (.leaf (0)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (3)) (.leaf (1))) (.branch 63 (.leaf (5)) (.leaf (8))))))))
  code := certificateP9_5151
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-22)) (.leaf (-24)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.branch 56 (.leaf (-39)) (.leaf (-40)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-4)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 52 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 41 (.leaf (-24)) (.branch 54 (.leaf (-23)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 62 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-40)) (.leaf (-35))) (.branch 59 (.leaf (-30)) (.leaf (-25)))) (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 38 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_294_5152 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (7))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (3))) (.branch 19 (.leaf (1)) (.leaf (8)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (0))) (.branch 23 (.leaf (4)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (5))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (1))) (.branch 31 (.leaf (7)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (1)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (0))) (.branch 39 (.leaf (4)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (8))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (5)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (1)) (.leaf (7)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (3))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (6))) (.branch 59 (.leaf (0)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (4)) (.leaf (1))) (.branch 63 (.leaf (8)) (.leaf (3))))))))
  code := certificateP9_5152
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 36 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-22)) (.leaf (-24)))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 36 (.leaf (-4)) (.branch 56 (.leaf (-6)) (.leaf (-7))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-5)))) (.branch 45 (.leaf (-7)) (.branch 61 (.leaf (-9)) (.leaf (-11))))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-49)) (.leaf (-50)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (-16))) (.branch 58 (.leaf (-17)) (.leaf (-18)))),
  (.branch 31 (.branch 10 (.leaf (0)) (.leaf (-34))) (.branch 52 (.leaf (-35)) (.leaf (-36)))),
  (.branch 20 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 52 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 41 (.leaf (-24)) (.branch 54 (.leaf (-23)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-7)) (.leaf (-6))) (.branch 59 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.branch 61 (.leaf (-3)) (.leaf (-2))) (.branch 63 (.leaf (-1)) (.leaf (0))))),
  (.branch 62 (.leaf (-11)) (.branch 63 (.leaf (-10)) (.leaf (-9)))),
  (.branch 55 (.branch 51 (.branch 49 (.branch 27 (.leaf (-50)) (.leaf (-48))) (.branch 50 (.leaf (-45)) (.leaf (-42)))) (.branch 53 (.branch 52 (.leaf (-39)) (.leaf (-36))) (.branch 54 (.leaf (-33)) (.leaf (-30))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-27)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 58 (.branch 55 (.branch 53 (.leaf (-36)) (.branch 54 (.leaf (-33)) (.leaf (-30)))) (.branch 56 (.leaf (-27)) (.branch 57 (.leaf (-24)) (.leaf (-21))))) (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 21 (.leaf (-4)) (.leaf (-3)))]
def witnessP9_294_5153 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (1))) (.branch 23 (.leaf (8)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 31 (.leaf (1)) (.leaf (7))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (1)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (0))) (.branch 39 (.leaf (5)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (4)) (.leaf (0))) (.branch 43 (.leaf (2)) (.leaf (8)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (3))) (.branch 47 (.leaf (0)) (.leaf (5)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (4)))) (.branch 54 (.branch 53 (.leaf (6)) (.leaf (1))) (.branch 55 (.leaf (7)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (5)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (4))) (.branch 63 (.leaf (1)) (.leaf (8))))))))
  code := certificateP9_5153
  counts := ![(.branch 29 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 56 (.branch 51 (.leaf (11)) (.leaf (12))) (.branch 61 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 27 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 19 (.leaf (-26)) (.leaf (-27)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-20)) (.leaf (-22)))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (-5)) (.leaf (-6)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (-4))) (.branch 48 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.branch 32 (.leaf (-10)) (.leaf (-12)))),
  (.leaf (0))]
  high := ![(.branch 57 (.branch 52 (.leaf (-27)) (.leaf (-24))) (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 36 (.leaf (-11)) (.branch 59 (.leaf (-10)) (.leaf (-7)))),
  (.branch 61 (.branch 51 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 58 (.branch 47 (.leaf (-22)) (.leaf (-21))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 63 (.leaf (-6)) (.leaf (-3))),
  (.branch 61 (.branch 49 (.leaf (-7)) (.leaf (-6))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.branch 56 (.branch 33 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 61 (.branch 60 (.leaf (-7)) (.leaf (-6))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3)))))),
  (.leaf (0))]
def witnessP9_294_5154 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (4))) (.branch 15 (.leaf (0)) (.leaf (8)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (7)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (4))) (.branch 31 (.leaf (1)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (1)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (8)) (.leaf (0))) (.branch 39 (.leaf (2)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (6)) (.leaf (0))) (.branch 43 (.leaf (3)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (4))) (.branch 47 (.leaf (0)) (.leaf (7)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (8)) (.leaf (1))) (.branch 59 (.leaf (3)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (4))) (.branch 63 (.leaf (1)) (.leaf (6))))))))
  code := certificateP9_5154
  counts := ![(.branch 28 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 56 (.branch 51 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 19 (.leaf (-26)) (.branch 28 (.leaf (-27)) (.leaf (-28))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 21 (.leaf (0)) (.branch 41 (.leaf (-1)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (-17)) (.leaf (-19)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (-6))) (.branch 57 (.leaf (-7)) (.leaf (-9))))]
  high := ![(.branch 62 (.branch 61 (.leaf (-28)) (.leaf (-21))) (.branch 63 (.leaf (-14)) (.leaf (-7)))),
  (.branch 45 (.leaf (-12)) (.branch 59 (.leaf (-10)) (.leaf (-7)))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 61 (.branch 59 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 43 (.branch 42 (.leaf (-3)) (.leaf (-2))) (.branch 44 (.leaf (-1)) (.leaf (0)))),
  (.branch 55 (.branch 51 (.branch 49 (.branch 26 (.leaf (-19)) (.leaf (-18))) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 53 (.branch 52 (.leaf (-15)) (.leaf (-14))) (.branch 54 (.leaf (-13)) (.leaf (-12))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8)))) (.branch 61 (.branch 60 (.leaf (-7)) (.leaf (-6))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))))),
  (.branch 60 (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7)))) (.branch 62 (.branch 61 (.leaf (-6)) (.leaf (-5))) (.branch 63 (.leaf (-4)) (.leaf (-3)))))]
def witnessP9_294_5155 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (7)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (3))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (6)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (1)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (2)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (5)) (.leaf (0))) (.branch 43 (.leaf (3)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (0))) (.branch 47 (.leaf (8)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (4)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (3))) (.branch 55 (.leaf (2)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (5)) (.leaf (1))) (.branch 59 (.leaf (3)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (1))) (.branch 63 (.leaf (6)) (.leaf (3))))))))
  code := certificateP9_5155
  counts := ![(.branch 28 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 56 (.branch 51 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 30 (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 16 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 38 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.leaf (0)) (.branch 63 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 14 (.leaf (-29)) (.leaf (-30)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 21 (.leaf (-12)) (.branch 30 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.branch 31 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-49))),
  (.branch 47 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 61 (.branch 47 (.leaf (-30)) (.leaf (-28))) (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 63 (.leaf (-14)) (.leaf (-7))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 39 (.branch 27 (.branch 21 (.branch 18 (.branch 16 (.leaf (-49)) (.branch 17 (.leaf (-48)) (.leaf (-47)))) (.branch 19 (.leaf (-46)) (.branch 20 (.leaf (-45)) (.leaf (-44))))) (.branch 24 (.branch 22 (.leaf (-43)) (.branch 23 (.leaf (-42)) (.leaf (-41)))) (.branch 25 (.leaf (-40)) (.branch 26 (.leaf (-39)) (.leaf (-38)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-37)) (.branch 29 (.leaf (-36)) (.leaf (-35)))) (.branch 31 (.leaf (-34)) (.branch 32 (.leaf (-33)) (.leaf (-32))))) (.branch 36 (.branch 34 (.leaf (-31)) (.branch 35 (.leaf (-30)) (.leaf (-29)))) (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26))))))) (.branch 51 (.branch 45 (.branch 42 (.branch 40 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-23)))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))) (.branch 48 (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17)))) (.branch 49 (.leaf (-16)) (.branch 50 (.leaf (-15)) (.leaf (-14)))))) (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 55 (.branch 51 (.branch 49 (.branch 48 (.leaf (-17)) (.leaf (-16))) (.branch 50 (.leaf (-15)) (.leaf (-14)))) (.branch 53 (.branch 52 (.leaf (-13)) (.leaf (-12))) (.branch 54 (.leaf (-11)) (.leaf (-10))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_294_5156 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (8))) (.branch 11 (.leaf (0)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (5))) (.branch 19 (.leaf (1)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (6))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (7))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (1))) (.branch 31 (.leaf (5)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (1)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (0))) (.branch 39 (.leaf (3)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (8))) (.branch 43 (.leaf (0)) (.leaf (5)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (6))) (.branch 51 (.leaf (1)) (.leaf (4)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (5))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (7))) (.branch 59 (.leaf (0)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (4)) (.leaf (1))) (.branch 63 (.leaf (6)) (.leaf (3))))))))
  code := certificateP9_5156
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.leaf (0)) (.branch 58 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-22)) (.leaf (-24)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.branch 56 (.leaf (-39)) (.leaf (-40)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-4)) (.leaf (-8)))),
  (.branch 26 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.leaf (-22)))]
  high := ![(.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 52 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 41 (.leaf (-24)) (.branch 54 (.leaf (-23)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 56 (.leaf (-1)) (.leaf (0))),
  (.branch 62 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-40)) (.leaf (-35))) (.branch 59 (.leaf (-30)) (.leaf (-25)))) (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 38 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 47 (.branch 44 (.branch 43 (.leaf (-22)) (.leaf (-21))) (.branch 45 (.leaf (-20)) (.branch 46 (.leaf (-19)) (.leaf (-18))))) (.branch 50 (.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_294_5157 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (8))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (7)) (.leaf (5))) (.branch 23 (.leaf (0)) (.leaf (6))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (8))) (.branch 31 (.leaf (1)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (3))) (.branch 35 (.leaf (1)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (6))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (5)) (.leaf (1))) (.branch 43 (.leaf (3)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (8))) (.branch 47 (.leaf (1)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (1)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (7)) (.leaf (4))) (.branch 55 (.leaf (0)) (.leaf (6))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (2)) (.leaf (1))) (.branch 59 (.leaf (5)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (3)) (.leaf (8))) (.branch 63 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_5157
  counts := ![(.branch 28 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.leaf (7))))),
  (.branch 34 (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.leaf (7))))),
  (.branch 36 (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 64 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 35 (.leaf (-5)) (.branch 51 (.leaf (-7)) (.leaf (-9))))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-50)) (.leaf (-51)))) (.branch 29 (.leaf (-52)) (.branch 38 (.leaf (-53)) (.leaf (-54))))),
  (.branch 6 (.leaf (0)) (.leaf (-22))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))) (.branch 45 (.branch 36 (.leaf (-3)) (.leaf (-4))) (.branch 54 (.leaf (-5)) (.leaf (-6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-36))) (.branch 22 (.leaf (-37)) (.leaf (-38)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 61 (.branch 50 (.leaf (-13)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-9)),
  (.branch 60 (.branch 58 (.branch 39 (.leaf (-54)) (.leaf (-49))) (.branch 59 (.leaf (-42)) (.leaf (-35)))) (.branch 62 (.branch 61 (.leaf (-28)) (.leaf (-21))) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 62 (.branch 7 (.leaf (-22)) (.leaf (-21))) (.branch 63 (.leaf (-14)) (.leaf (-7)))),
  (.branch 55 (.leaf (-6)) (.leaf (0))),
  (.branch 61 (.branch 23 (.leaf (-38)) (.branch 60 (.leaf (-35)) (.leaf (-28)))) (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_294_5158 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (6)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (3)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (7)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (3)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (5)) (.leaf (1))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (3)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (4)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (2))) (.branch 43 (.leaf (3)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (2))) (.branch 47 (.leaf (6)) (.leaf (1)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (3)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (8)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (3)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (2))) (.branch 63 (.leaf (5)) (.leaf (1))))))))
  code := certificateP9_5158
  counts := ![(.branch 29 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 48 (.branch 40 (.branch 36 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 52 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.branch 64 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 31 (.leaf (0)) (.branch 63 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 55 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-25))),
  (.branch 31 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-17))),
  (.branch 23 (.leaf (0)) (.leaf (-41))),
  (.branch 55 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.branch 45 (.branch 42 (.branch 40 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-23)))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))) (.branch 48 (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17)))) (.branch 49 (.leaf (-16)) (.branch 50 (.leaf (-15)) (.leaf (-14)))))) (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1)),
  (.branch 55 (.branch 51 (.branch 49 (.branch 48 (.leaf (-17)) (.leaf (-16))) (.branch 50 (.leaf (-15)) (.leaf (-14)))) (.branch 53 (.branch 52 (.leaf (-13)) (.leaf (-12))) (.branch 54 (.leaf (-11)) (.leaf (-10))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 33 (.branch 28 (.branch 25 (.branch 24 (.leaf (-41)) (.leaf (-40))) (.branch 26 (.leaf (-39)) (.branch 27 (.leaf (-38)) (.leaf (-37))))) (.branch 30 (.branch 29 (.leaf (-36)) (.leaf (-35))) (.branch 31 (.leaf (-34)) (.branch 32 (.leaf (-33)) (.leaf (-32)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (-31)) (.leaf (-30))) (.branch 36 (.leaf (-29)) (.branch 37 (.leaf (-28)) (.leaf (-27))))) (.branch 40 (.branch 39 (.leaf (-26)) (.leaf (-25))) (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22))))))) (.branch 53 (.branch 48 (.branch 45 (.branch 44 (.leaf (-21)) (.leaf (-20))) (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17))))) (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_294_5159 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (6))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (7)) (.leaf (1))) (.branch 15 (.leaf (4)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (6)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (0))) (.branch 23 (.leaf (4)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (5))) (.branch 27 (.leaf (0)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (8)) (.leaf (1))) (.branch 31 (.leaf (3)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (5)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (0))) (.branch 39 (.leaf (3)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (4))) (.branch 43 (.leaf (0)) (.leaf (5)))) (.branch 46 (.branch 45 (.leaf (7)) (.leaf (1))) (.branch 47 (.leaf (6)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (4)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (0))) (.branch 55 (.leaf (6)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (2)) (.leaf (3))) (.branch 59 (.leaf (0)) (.leaf (4)))) (.branch 62 (.branch 61 (.leaf (8)) (.leaf (1))) (.branch 63 (.leaf (5)) (.leaf (6))))))))
  code := certificateP9_5159
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 14 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 36 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 51 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 60 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.leaf (7))))),
  (.branch 37 (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 55 (.branch 47 (.leaf (4)) (.leaf (5))) (.branch 64 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 29 (.leaf (0)) (.branch 61 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.leaf (-15)))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-6)))) (.branch 40 (.leaf (-7)) (.branch 56 (.leaf (-8)) (.leaf (-9))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-31)) (.leaf (-32)))) (.branch 39 (.leaf (-33)) (.branch 48 (.leaf (-35)) (.leaf (-36))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (-21))) (.branch 32 (.leaf (-23)) (.leaf (-24)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 55 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-19))),
  (.branch 29 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.leaf (-9)) (.branch 63 (.leaf (-8)) (.leaf (-6)))),
  (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 49 (.leaf (-36)) (.branch 59 (.leaf (-32)) (.leaf (-27)))) (.branch 62 (.branch 61 (.leaf (-22)) (.leaf (-17))) (.branch 63 (.leaf (-12)) (.leaf (-7))))),
  (.branch 61 (.branch 33 (.leaf (-24)) (.leaf (-22))) (.branch 62 (.leaf (-17)) (.branch 63 (.leaf (-12)) (.leaf (-7))))),
  (.branch 17 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-7)))),
  (.branch 56 (.leaf (-1)) (.leaf (0))),
  (.branch 54 (.branch 49 (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_294_5160 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (5))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (6)) (.leaf (8)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (2)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (7))) (.branch 19 (.leaf (4)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (6))) (.branch 23 (.leaf (1)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (8)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (4))) (.branch 31 (.leaf (7)) (.leaf (6))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (3)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (8)) (.leaf (5))) (.branch 39 (.leaf (0)) (.leaf (4))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (1))) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (3))) (.branch 47 (.leaf (2)) (.leaf (5)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (8))) (.branch 51 (.leaf (4)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (6))) (.branch 55 (.leaf (1)) (.leaf (3))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (7)) (.leaf (0))) (.branch 59 (.leaf (5)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (4))) (.branch 63 (.leaf (8)) (.leaf (6))))))))
  code := certificateP9_5160
  counts := ![(.branch 26 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 33 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 36 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.leaf (-27))) (.branch 13 (.leaf (-29)) (.leaf (-31)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-12))) (.branch 29 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-22)) (.leaf (-23)))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (-23)) (.leaf (-24)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-16)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-39))),
  (.branch 12 (.leaf (0)) (.branch 37 (.leaf (-4)) (.leaf (-7))))]
  high := ![(.branch 60 (.branch 46 (.leaf (-31)) (.branch 59 (.leaf (-30)) (.leaf (-25)))) (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 61 (.branch 54 (.leaf (-23)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-24)) (.leaf (-21))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 52 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 49 (.leaf (-16)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 58 (.branch 19 (.branch 6 (.leaf (-39)) (.leaf (-38))) (.branch 32 (.leaf (-37)) (.branch 45 (.leaf (-36)) (.leaf (-35))))) (.branch 61 (.branch 59 (.leaf (-30)) (.branch 60 (.leaf (-25)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 38 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5))))]
def witnessP9_294_5161 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (7))) (.branch 15 (.leaf (4)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (3)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (8))) (.branch 31 (.leaf (5)) (.leaf (1))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (3)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (3)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (6)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (7))) (.branch 47 (.leaf (4)) (.leaf (1)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (3)) (.leaf (5)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (4)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (8))) (.branch 63 (.leaf (6)) (.leaf (1))))))))
  code := certificateP9_5161
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 35 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.branch 62 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 28 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 12 (.leaf (-5)) (.branch 23 (.leaf (-6)) (.leaf (-7))))) (.branch 44 (.branch 39 (.leaf (-8)) (.leaf (-9))) (.branch 55 (.leaf (-10)) (.branch 60 (.leaf (-11)) (.leaf (-12)))))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (-20)) (.leaf (-21)))),
  (.branch 9 (.leaf (0)) (.leaf (-37))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (-4)) (.leaf (-5)))),
  (.branch 14 (.leaf (0)) (.leaf (-18))),
  (.branch 30 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 59 (.leaf (-2)) (.leaf (0))),
  (.branch 62 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-11))) (.branch 63 (.leaf (-10)) (.leaf (-9)))),
  (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.branch 54 (.branch 10 (.leaf (-37)) (.branch 53 (.leaf (-36)) (.leaf (-33)))) (.branch 55 (.leaf (-30)) (.branch 56 (.leaf (-27)) (.leaf (-24))))) (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 42 (.leaf (-5)) (.leaf (-3))),
  (.branch 55 (.branch 50 (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 52 (.branch 51 (.leaf (-14)) (.leaf (-13))) (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_294_5162 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (5))) (.branch 7 (.leaf (7)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (6))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (4))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (7)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (0))) (.branch 23 (.leaf (2)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (8))) (.branch 27 (.leaf (3)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (6)) (.leaf (7))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (1)) (.leaf (3))) (.branch 35 (.leaf (4)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (5))) (.branch 39 (.leaf (8)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (3)) (.leaf (6))) (.branch 43 (.leaf (0)) (.leaf (2)))) (.branch 46 (.branch 45 (.leaf (7)) (.leaf (4))) (.branch 47 (.leaf (1)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (5)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (8)))) (.branch 54 (.branch 53 (.leaf (6)) (.leaf (1))) (.branch 55 (.leaf (3)) (.leaf (4))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (7))) (.branch 59 (.leaf (2)) (.leaf (5)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (3))) (.branch 63 (.leaf (6)) (.leaf (8))))))))
  code := certificateP9_5162
  counts := ![(.branch 29 (.branch 8 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 50 (.leaf (7)) (.branch 57 (.leaf (8)) (.leaf (9)))))),
  (.branch 33 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 54 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 37 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 59 (.leaf (8)) (.leaf (9)))))),
  (.branch 34 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 41 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 29 (.branch 8 (.branch 1 (.leaf (0)) (.leaf (-55))) (.branch 15 (.leaf (-56)) (.branch 22 (.leaf (-57)) (.leaf (-58))))) (.branch 43 (.branch 36 (.leaf (-59)) (.leaf (-60))) (.branch 50 (.leaf (-61)) (.branch 57 (.leaf (-62)) (.leaf (-63)))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-28))) (.branch 18 (.leaf (-29)) (.branch 25 (.leaf (-30)) (.leaf (-31))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-46))) (.branch 16 (.leaf (-47)) (.leaf (-48)))) (.branch 37 (.branch 30 (.leaf (-49)) (.leaf (-50))) (.branch 44 (.leaf (-51)) (.branch 51 (.leaf (-52)) (.leaf (-53)))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-19))) (.branch 19 (.leaf (-20)) (.leaf (-21)))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (-23)) (.leaf (-24)))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.branch 32 (.leaf (-29)) (.leaf (-32)))),
  (.leaf (0))]
  high := ![(.branch 60 (.branch 58 (.leaf (-63)) (.branch 59 (.leaf (-54)) (.leaf (-45)))) (.branch 62 (.branch 61 (.leaf (-36)) (.leaf (-27))) (.branch 63 (.leaf (-18)) (.leaf (-9))))),
  (.branch 62 (.branch 26 (.leaf (-31)) (.leaf (-27))) (.branch 63 (.leaf (-18)) (.leaf (-9)))),
  (.branch 61 (.branch 52 (.leaf (-53)) (.branch 60 (.leaf (-45)) (.leaf (-36)))) (.branch 62 (.leaf (-27)) (.branch 63 (.leaf (-18)) (.leaf (-9))))),
  (.branch 20 (.leaf (-21)) (.branch 63 (.leaf (-18)) (.leaf (-9)))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-24)) (.leaf (-21))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.branch 39 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 60 (.branch 46 (.branch 33 (.leaf (-32)) (.leaf (-31))) (.branch 59 (.leaf (-30)) (.leaf (-25)))) (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0))]
def witnessP9_294_5163 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (3)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (4)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (2)) (.leaf (8))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (1)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (3)) (.leaf (1))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (4)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (2)) (.leaf (6))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (3))) (.branch 43 (.leaf (1)) (.leaf (4)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (0))) (.branch 47 (.leaf (3)) (.leaf (1)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (4)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (7))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (1)) (.leaf (4)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (0))) (.branch 63 (.leaf (3)) (.leaf (1))))))))
  code := certificateP9_5163
  counts := ![(.branch 30 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 32 (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-56))),
  (.branch 40 (.leaf (0)) (.leaf (-24))),
  (.branch 56 (.leaf (0)) (.leaf (-8))),
  (.branch 24 (.leaf (0)) (.leaf (-40)))]
  high := ![(.branch 58 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 54 (.leaf (-1)) (.leaf (0))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 61 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 22 (.branch 15 (.branch 11 (.branch 9 (.leaf (-56)) (.branch 10 (.leaf (-55)) (.leaf (-54)))) (.branch 13 (.branch 12 (.leaf (-53)) (.leaf (-52))) (.branch 14 (.leaf (-51)) (.leaf (-50))))) (.branch 18 (.branch 16 (.leaf (-49)) (.branch 17 (.leaf (-48)) (.leaf (-47)))) (.branch 20 (.branch 19 (.leaf (-46)) (.leaf (-45))) (.branch 21 (.leaf (-44)) (.leaf (-43)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-42)) (.branch 24 (.leaf (-41)) (.leaf (-40)))) (.branch 27 (.branch 26 (.leaf (-39)) (.leaf (-38))) (.branch 28 (.leaf (-37)) (.leaf (-36))))) (.branch 32 (.branch 30 (.leaf (-35)) (.branch 31 (.leaf (-34)) (.leaf (-33)))) (.branch 34 (.branch 33 (.leaf (-32)) (.leaf (-31))) (.branch 35 (.leaf (-30)) (.leaf (-29))))))) (.branch 50 (.branch 43 (.branch 39 (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26)))) (.branch 41 (.branch 40 (.leaf (-25)) (.leaf (-24))) (.branch 42 (.leaf (-23)) (.leaf (-22))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19)))) (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 52 (.branch 46 (.branch 43 (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22)))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))))) (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.branch 34 (.branch 29 (.branch 26 (.branch 25 (.leaf (-40)) (.leaf (-39))) (.branch 27 (.leaf (-38)) (.branch 28 (.leaf (-37)) (.leaf (-36))))) (.branch 31 (.branch 30 (.leaf (-35)) (.leaf (-34))) (.branch 32 (.leaf (-33)) (.branch 33 (.leaf (-32)) (.leaf (-31)))))) (.branch 39 (.branch 36 (.branch 35 (.leaf (-30)) (.leaf (-29))) (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26))))) (.branch 41 (.branch 40 (.leaf (-25)) (.leaf (-24))) (.branch 42 (.leaf (-23)) (.branch 43 (.leaf (-22)) (.leaf (-21))))))) (.branch 54 (.branch 49 (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16))))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_294_5164 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (3)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (4)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (2)) (.leaf (7))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (1)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (3)) (.leaf (1))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (4)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (2)) (.leaf (6))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (3))) (.branch 43 (.leaf (1)) (.leaf (5)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (0))) (.branch 47 (.leaf (3)) (.leaf (1)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (4)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (8))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (1)) (.leaf (5)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (0))) (.branch 63 (.leaf (3)) (.leaf (1))))))))
  code := certificateP9_5164
  counts := ![(.branch 30 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 49 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 32 (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-24))),
  (.branch 24 (.leaf (0)) (.leaf (-40))),
  (.branch 56 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 58 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 54 (.leaf (-1)) (.leaf (0))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.branch 46 (.branch 43 (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22)))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))))) (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 34 (.branch 29 (.branch 26 (.branch 25 (.leaf (-40)) (.leaf (-39))) (.branch 27 (.leaf (-38)) (.branch 28 (.leaf (-37)) (.leaf (-36))))) (.branch 31 (.branch 30 (.leaf (-35)) (.leaf (-34))) (.branch 32 (.leaf (-33)) (.branch 33 (.leaf (-32)) (.leaf (-31)))))) (.branch 39 (.branch 36 (.branch 35 (.leaf (-30)) (.leaf (-29))) (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26))))) (.branch 41 (.branch 40 (.leaf (-25)) (.leaf (-24))) (.branch 42 (.leaf (-23)) (.branch 43 (.leaf (-22)) (.leaf (-21))))))) (.branch 54 (.branch 49 (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16))))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_294_5165 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (6))) (.branch 15 (.leaf (3)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (5)) (.leaf (8)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (4)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (6))) (.branch 31 (.leaf (7)) (.leaf (1))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (4)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (5)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (8)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (4)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (6))) (.branch 47 (.leaf (3)) (.leaf (1)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (5)) (.leaf (7)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (5)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (6))) (.branch 63 (.leaf (8)) (.leaf (1))))))))
  code := certificateP9_5165
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (-20)) (.leaf (-21)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 44 (.leaf (-10)) (.leaf (-11)))),
  (.branch 28 (.branch 7 (.leaf (0)) (.leaf (-4))) (.branch 60 (.leaf (-5)) (.leaf (-6)))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-37))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 59 (.leaf (-2)) (.leaf (0))),
  (.branch 62 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8)))) (.branch 61 (.branch 60 (.leaf (-7)) (.leaf (-6))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 62 (.branch 61 (.leaf (-6)) (.leaf (-5))) (.branch 63 (.leaf (-4)) (.leaf (-3)))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.branch 54 (.branch 10 (.leaf (-37)) (.branch 53 (.leaf (-36)) (.leaf (-33)))) (.branch 55 (.leaf (-30)) (.branch 56 (.leaf (-27)) (.leaf (-24))))) (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 42 (.leaf (-5)) (.leaf (-3)))]
def witnessP9_294_5166 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (7))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (6))) (.branch 11 (.leaf (8)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (0)) (.leaf (7)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (2))) (.branch 19 (.leaf (1)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (8))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (7)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (6)) (.leaf (8))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (1)) (.leaf (2))) (.branch 35 (.leaf (4)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (7))) (.branch 39 (.leaf (5)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (6))) (.branch 43 (.leaf (8)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (1)) (.leaf (7)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (5)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (6)) (.leaf (8))) (.branch 55 (.leaf (1)) (.leaf (4))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (7)) (.leaf (5)))) (.branch 62 (.branch 61 (.leaf (3)) (.leaf (1))) (.branch 63 (.leaf (6)) (.leaf (8))))))))
  code := certificateP9_5166
  counts := ![(.branch 30 (.branch 8 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 37 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 58 (.leaf (8)) (.leaf (9)))))),
  (.branch 33 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6)))))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-55))) (.branch 15 (.leaf (-56)) (.leaf (-57)))),
  (.branch 26 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-19))) (.branch 19 (.leaf (-20)) (.leaf (-21)))) (.branch 40 (.branch 33 (.leaf (-22)) (.leaf (-23))) (.branch 47 (.leaf (-24)) (.leaf (-25))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (-23)) (.leaf (-24)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-11)) (.leaf (-13)))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-16)))),
  (.leaf (0))]
  high := ![(.branch 60 (.branch 16 (.leaf (-57)) (.branch 59 (.leaf (-54)) (.leaf (-45)))) (.branch 62 (.branch 61 (.leaf (-36)) (.leaf (-27))) (.branch 63 (.leaf (-18)) (.leaf (-9))))),
  (.branch 48 (.leaf (-25)) (.branch 63 (.leaf (-18)) (.leaf (-9)))),
  (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 62 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-24)) (.leaf (-21))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.branch 50 (.leaf (-13)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 61 (.branch 49 (.leaf (-16)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0))]
def witnessP9_294_5167 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (5)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (1))) (.branch 23 (.leaf (4)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (7)) (.leaf (2))) (.branch 27 (.leaf (1)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (1)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (5)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (0))) (.branch 39 (.leaf (4)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (6)) (.leaf (2))) (.branch 43 (.leaf (0)) (.leaf (5)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (3))) (.branch 47 (.leaf (0)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (2))) (.branch 51 (.leaf (5)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (3)) (.leaf (1))) (.branch 55 (.leaf (4)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (8)) (.leaf (2))) (.branch 59 (.leaf (1)) (.leaf (5)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (3))) (.branch 63 (.leaf (1)) (.leaf (4))))))))
  code := certificateP9_5167
  counts := ![(.branch 29 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 43 (.leaf (9)) (.leaf (10)))) (.branch 56 (.branch 52 (.leaf (11)) (.leaf (12))) (.branch 61 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 40 (.branch 36 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 59 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 57 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-25))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-23))),
  (.branch 25 (.leaf (0)) (.leaf (-39))),
  (.branch 57 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 57 (.branch 34 (.leaf (-25)) (.leaf (-24))) (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 50 (.leaf (-9)) (.leaf (-7))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 56 (.leaf (-1)) (.leaf (0))),
  (.branch 61 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.branch 46 (.branch 43 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))))) (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 34 (.branch 29 (.branch 27 (.branch 26 (.leaf (-39)) (.leaf (-38))) (.branch 28 (.leaf (-37)) (.leaf (-36)))) (.branch 31 (.branch 30 (.leaf (-35)) (.leaf (-34))) (.branch 32 (.leaf (-33)) (.branch 33 (.leaf (-32)) (.leaf (-31)))))) (.branch 39 (.branch 36 (.branch 35 (.leaf (-30)) (.leaf (-29))) (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26))))) (.branch 41 (.branch 40 (.leaf (-25)) (.leaf (-24))) (.branch 42 (.leaf (-23)) (.branch 43 (.leaf (-22)) (.leaf (-21))))))) (.branch 54 (.branch 49 (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16))))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_294_5168 : CycleWitness 9 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (7))) (.branch 11 (.leaf (8)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (6)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (2))) (.branch 23 (.leaf (5)) (.leaf (7))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (8)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (6)) (.leaf (1))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (5)) (.leaf (7)))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (4))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (6))) (.branch 43 (.leaf (8)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (3)) (.leaf (0))) (.branch 47 (.leaf (5)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (7)) (.leaf (1))) (.branch 51 (.leaf (4)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (3)) (.leaf (2))) (.branch 55 (.leaf (5)) (.leaf (6))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (8)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (7)) (.leaf (1))))))))
  code := certificateP9_5168
  counts := ![(.branch 26 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 33 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 38 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 62 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.leaf (-27))) (.branch 26 (.leaf (-29)) (.leaf (-30)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 18 (.leaf (-2)) (.branch 50 (.leaf (-3)) (.leaf (-4))))),
  (.branch 2 (.leaf (0)) (.branch 34 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 55 (.leaf (-23)) (.leaf (-28)))),
  (.branch 4 (.leaf (0)) (.branch 42 (.leaf (-9)) (.leaf (-10)))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 61 (.branch 59 (.leaf (-30)) (.branch 60 (.leaf (-25)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 58 (.branch 51 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-1)) (.leaf (0)))),
  (.branch 62 (.branch 61 (.leaf (-10)) (.leaf (-8))) (.branch 63 (.leaf (-6)) (.leaf (-4)))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-28)) (.leaf (-26))) (.branch 58 (.leaf (-24)) (.leaf (-22)))) (.branch 61 (.branch 60 (.leaf (-20)) (.leaf (-18))) (.branch 62 (.leaf (-16)) (.branch 63 (.leaf (-14)) (.leaf (-12)))))),
  (.branch 59 (.branch 57 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 58 (.leaf (-8)) (.leaf (-7)))) (.branch 61 (.branch 60 (.leaf (-6)) (.leaf (-5))) (.branch 62 (.leaf (-4)) (.branch 63 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 50 (.leaf (-3)) (.leaf (-2))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_294 : Fin 46 → CycleWitness 9 := ![witnessP9_294_5123, witnessP9_294_5124, witnessP9_294_5125, witnessP9_294_5126, witnessP9_294_5127, witnessP9_294_5128, witnessP9_294_5129, witnessP9_294_5130, witnessP9_294_5131, witnessP9_294_5132, witnessP9_294_5133, witnessP9_294_5134, witnessP9_294_5135, witnessP9_294_5136, witnessP9_294_5137, witnessP9_294_5138, witnessP9_294_5139, witnessP9_294_5140, witnessP9_294_5141, witnessP9_294_5142, witnessP9_294_5143, witnessP9_294_5144, witnessP9_294_5145, witnessP9_294_5146, witnessP9_294_5147, witnessP9_294_5148, witnessP9_294_5149, witnessP9_294_5150, witnessP9_294_5151, witnessP9_294_5152, witnessP9_294_5153, witnessP9_294_5154, witnessP9_294_5155, witnessP9_294_5156, witnessP9_294_5157, witnessP9_294_5158, witnessP9_294_5159, witnessP9_294_5160, witnessP9_294_5161, witnessP9_294_5162, witnessP9_294_5163, witnessP9_294_5164, witnessP9_294_5165, witnessP9_294_5166, witnessP9_294_5167, witnessP9_294_5168]
end RealPinwheel.FiveSixths


