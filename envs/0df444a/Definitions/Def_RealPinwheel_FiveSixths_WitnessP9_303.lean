-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_303
-- name    : RealPinwheel_FiveSixths_WitnessP9_303
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:27:29.511192+00:00
-- url     : https://prove2.me/theorems/cd122a8b-f1ce-4e88-8768-f5b6f6ef997c
-- title:
--   Exact witness block P9_303
-- statement:
--   These exact witnesses represent words 5568 through 5619 of source certificate file P9. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 5568–5619; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/P9.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateP9
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessP9_303_5567 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (7)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (5)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (6)))) (.branch 34 (.branch 33 (.leaf (4)) (.leaf (0))) (.branch 35 (.leaf (2)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (5)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (4)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (3)) (.branch 45 (.leaf (0)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (8)) (.leaf (1))) (.branch 49 (.leaf (0)) (.leaf (3))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (2)) (.leaf (4))) (.branch 53 (.leaf (0)) (.leaf (5)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5567
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 35 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 30 (.leaf (-8)) (.leaf (-9)))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 48 (.leaf (-5)) (.leaf (-6)))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (-1))) (.branch 51 (.leaf (-2)) (.leaf (-3)))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 50 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-17)) (.leaf (-19)))),
  (.branch 10 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.leaf (-26))),
  (.branch 18 (.leaf (0)) (.leaf (-40))),
  (.branch 47 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 42 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-5)))),
  (.branch 56 (.branch 49 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 51 (.leaf (-4)) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.branch 54 (.branch 43 (.leaf (-19)) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3))))),
  (.branch 55 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.branch 45 (.branch 38 (.branch 35 (.branch 33 (.leaf (-26)) (.branch 34 (.leaf (-25)) (.leaf (-24)))) (.branch 36 (.leaf (-23)) (.branch 37 (.leaf (-22)) (.leaf (-21))))) (.branch 41 (.branch 39 (.leaf (-20)) (.branch 40 (.leaf (-19)) (.leaf (-18)))) (.branch 43 (.branch 42 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-15)) (.leaf (-14)))))) (.branch 51 (.branch 48 (.branch 46 (.leaf (-13)) (.branch 47 (.leaf (-12)) (.leaf (-11)))) (.branch 49 (.leaf (-10)) (.branch 50 (.leaf (-9)) (.leaf (-8))))) (.branch 54 (.branch 52 (.leaf (-7)) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 28 (.branch 23 (.branch 20 (.branch 19 (.leaf (-40)) (.leaf (-39))) (.branch 21 (.leaf (-38)) (.branch 22 (.leaf (-37)) (.leaf (-36))))) (.branch 25 (.branch 24 (.leaf (-35)) (.leaf (-34))) (.branch 26 (.leaf (-33)) (.branch 27 (.leaf (-32)) (.leaf (-31)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-30)) (.leaf (-29))) (.branch 31 (.leaf (-28)) (.branch 32 (.leaf (-27)) (.leaf (-26))))) (.branch 35 (.branch 34 (.leaf (-25)) (.leaf (-24))) (.branch 36 (.leaf (-23)) (.branch 37 (.leaf (-22)) (.leaf (-21))))))) (.branch 48 (.branch 43 (.branch 40 (.branch 39 (.leaf (-20)) (.leaf (-19))) (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-17)) (.leaf (-16))))) (.branch 45 (.branch 44 (.leaf (-15)) (.leaf (-14))) (.branch 46 (.leaf (-13)) (.branch 47 (.leaf (-12)) (.leaf (-11)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-8)) (.branch 52 (.leaf (-7)) (.leaf (-6))))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 52 (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-10))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_303_5568 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (2))) (.branch 6 (.leaf (8)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (5)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (7))) (.branch 13 (.leaf (4)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (6)) (.branch 16 (.leaf (0)) (.leaf (8)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (3))) (.branch 20 (.leaf (5)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (7))) (.branch 24 (.leaf (4)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (6)) (.leaf (1))) (.branch 28 (.leaf (3)) (.leaf (8))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (5)))) (.branch 34 (.branch 33 (.leaf (4)) (.leaf (1))) (.branch 35 (.leaf (7)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (6)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (8))) (.branch 42 (.leaf (4)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (5)) (.branch 45 (.leaf (0)) (.leaf (7)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (3))) (.branch 49 (.leaf (6)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (1)) (.leaf (8))) (.branch 53 (.leaf (4)) (.leaf (0)))) (.branch 56 (.branch 55 (.leaf (5)) (.leaf (2))) (.branch 57 (.leaf (3)) (.leaf (7))))))))
  code := certificateP9_5568
  counts := ![(.branch 25 (.branch 11 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 30 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.leaf (7))))),
  (.branch 31 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 12 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 25 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 54 (.leaf (-5)) (.leaf (-6)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-19))) (.branch 18 (.leaf (-20)) (.branch 34 (.leaf (-21)) (.leaf (-23))))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 8 (.leaf (0)) (.branch 37 (.leaf (-2)) (.leaf (-3)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-6))) (.branch 42 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-13)) (.leaf (-16)))),
  (.branch 26 (.branch 3 (.leaf (0)) (.leaf (-43))) (.branch 49 (.leaf (-44)) (.leaf (-45)))),
  (.branch 23 (.leaf (0)) (.branch 46 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-28)) (.leaf (-31))))]
  high := ![(.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 54 (.branch 52 (.branch 35 (.leaf (-23)) (.leaf (-22))) (.branch 53 (.leaf (-19)) (.leaf (-16)))) (.branch 56 (.branch 55 (.leaf (-13)) (.leaf (-10))) (.branch 57 (.leaf (-7)) (.leaf (-4))))),
  (.branch 48 (.branch 6 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-7)) (.leaf (-4)))),
  (.leaf (-3)),
  (.branch 55 (.branch 43 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3))))),
  (.branch 56 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5)))),
  (.branch 53 (.branch 51 (.branch 50 (.leaf (-45)) (.leaf (-40))) (.branch 52 (.leaf (-35)) (.leaf (-30)))) (.branch 55 (.branch 54 (.leaf (-25)) (.leaf (-20))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 47 (.leaf (-2)) (.leaf (0))),
  (.branch 54 (.branch 18 (.leaf (-31)) (.branch 53 (.leaf (-30)) (.leaf (-25)))) (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5)))))]
def witnessP9_303_5569 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (7)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (4)) (.leaf (8)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (7))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (6))) (.branch 28 (.leaf (5)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (8)))) (.branch 34 (.branch 33 (.leaf (4)) (.leaf (0))) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (5)) (.branch 38 (.leaf (1)) (.leaf (3)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (6))) (.branch 42 (.leaf (4)) (.leaf (7)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (5)) (.leaf (0))) (.branch 49 (.leaf (3)) (.leaf (8))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (0)) (.leaf (4))) (.branch 53 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (6))) (.branch 57 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_5569
  counts := ![(.branch 26 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 55 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 36 (.leaf (-29)) (.leaf (-34)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-21)) (.leaf (-22)))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-17)) (.leaf (-19)))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 21 (.leaf (-18)) (.leaf (-21)))),
  (.branch 32 (.branch 14 (.leaf (0)) (.leaf (-7))) (.branch 50 (.leaf (-10)) (.leaf (-13))))]
  high := ![(.branch 52 (.branch 37 (.leaf (-34)) (.leaf (-33))) (.branch 56 (.leaf (-31)) (.branch 57 (.leaf (-24)) (.leaf (-17))))),
  (.branch 55 (.branch 39 (.leaf (-22)) (.branch 54 (.leaf (-20)) (.leaf (-16)))) (.branch 56 (.leaf (-12)) (.branch 57 (.leaf (-8)) (.leaf (-4))))),
  (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 54 (.branch 43 (.leaf (-19)) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3))))),
  (.branch 38 (.leaf (-5)) (.branch 48 (.leaf (-4)) (.leaf (-3)))),
  (.branch 42 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-2)))),
  (.branch 50 (.branch 46 (.branch 44 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 45 (.leaf (-19)) (.leaf (-18)))) (.branch 48 (.branch 47 (.leaf (-17)) (.leaf (-16))) (.branch 49 (.leaf (-15)) (.leaf (-14))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-13)) (.leaf (-12))) (.branch 53 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 54 (.branch 52 (.branch 51 (.leaf (-13)) (.leaf (-12))) (.branch 53 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6)))))]
def witnessP9_303_5570 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (7))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (6)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (1))) (.branch 20 (.leaf (8)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (6))) (.branch 24 (.leaf (1)) (.leaf (3)))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (2))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (1)) (.branch 31 (.leaf (3)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (7))) (.branch 35 (.leaf (1)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (6)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (1))) (.branch 42 (.leaf (5)) (.leaf (0)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (3)) (.branch 45 (.leaf (1)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (8)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (3)) (.leaf (6))) (.branch 53 (.leaf (0)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (4)) (.leaf (1))) (.branch 57 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_5570
  counts := ![(.branch 27 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 48 (.leaf (9)) (.branch 53 (.leaf (10)) (.leaf (11)))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 50 (.leaf (9)) (.branch 56 (.leaf (10)) (.leaf (11)))))),
  (.branch 29 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 37 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 58 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 16 (.leaf (-14)) (.branch 21 (.leaf (-16)) (.leaf (-17))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 45 (.leaf (-8)) (.branch 50 (.leaf (-9)) (.leaf (-10))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-14))) (.branch 33 (.leaf (-16)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.branch 37 (.leaf (-8)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (-8)) (.leaf (-9)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (-5))) (.branch 52 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-24))),
  (.branch 20 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 55 (.branch 54 (.leaf (-17)) (.leaf (-14))) (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-8)) (.leaf (-5))))),
  (.branch 51 (.leaf (-10)) (.branch 57 (.leaf (-8)) (.leaf (-5)))),
  (.branch 48 (.branch 34 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19)))) (.branch 56 (.branch 55 (.leaf (-18)) (.leaf (-15))) (.branch 57 (.leaf (-12)) (.leaf (-9))))),
  (.branch 52 (.branch 38 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7)))) (.branch 53 (.leaf (-4)) (.branch 54 (.leaf (-1)) (.leaf (0))))),
  (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))),
  (.branch 43 (.leaf (-3)) (.leaf (-2))),
  (.branch 55 (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3))))),
  (.branch 46 (.branch 40 (.branch 37 (.branch 35 (.leaf (-24)) (.branch 36 (.leaf (-23)) (.leaf (-22)))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-20)) (.leaf (-19))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))))) (.branch 52 (.branch 49 (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 53 (.branch 51 (.branch 50 (.leaf (-9)) (.leaf (-8))) (.branch 52 (.leaf (-7)) (.leaf (-6)))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_303_5571 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (7))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (2)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (6)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (2))) (.branch 20 (.leaf (8)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (5)) (.leaf (3))) (.branch 28 (.leaf (4)) (.leaf (1))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (1)))) (.branch 34 (.branch 33 (.leaf (3)) (.leaf (7))) (.branch 35 (.leaf (0)) (.leaf (6))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (1)) (.leaf (3)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (4))) (.branch 42 (.leaf (2)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (3)) (.branch 45 (.leaf (0)) (.leaf (5)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (2))) (.branch 49 (.leaf (8)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (3)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (0)))) (.branch 56 (.branch 55 (.leaf (6)) (.leaf (3))) (.branch 57 (.leaf (4)) (.leaf (1))))))))
  code := certificateP9_5571
  counts := ![(.branch 25 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 33 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 25 (.leaf (-23)) (.leaf (-24)))),
  (.branch 3 (.leaf (0)) (.branch 32 (.leaf (-2)) (.leaf (-3)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 24 (.leaf (-5)) (.branch 53 (.leaf (-6)) (.leaf (-7))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 44 (.leaf (-3)) (.leaf (-4)))),
  (.branch 12 (.leaf (0)) (.branch 41 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (-37)) (.leaf (-38)))),
  (.branch 36 (.branch 17 (.leaf (0)) (.leaf (-7))) (.branch 55 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.leaf (-24))),
  (.branch 20 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 56 (.branch 55 (.leaf (-24)) (.leaf (-18))) (.branch 57 (.leaf (-12)) (.leaf (-6)))),
  (.branch 54 (.branch 53 (.leaf (-3)) (.leaf (-2))) (.branch 55 (.leaf (-1)) (.leaf (0)))),
  (.branch 55 (.branch 54 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3))))),
  (.branch 57 (.leaf (-4)) (.leaf (-3))),
  (.branch 42 (.leaf (-4)) (.leaf (-3))),
  (.branch 51 (.branch 48 (.branch 27 (.leaf (-38)) (.branch 47 (.leaf (-36)) (.leaf (-33)))) (.branch 49 (.leaf (-30)) (.branch 50 (.leaf (-27)) (.leaf (-24))))) (.branch 54 (.branch 52 (.leaf (-21)) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))),
  (.branch 46 (.branch 40 (.branch 37 (.branch 35 (.leaf (-24)) (.branch 36 (.leaf (-23)) (.leaf (-22)))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-20)) (.leaf (-19))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))))) (.branch 52 (.branch 49 (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 53 (.branch 51 (.branch 50 (.leaf (-9)) (.leaf (-8))) (.branch 52 (.leaf (-7)) (.leaf (-6)))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_303_5572 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (7))) (.branch 6 (.leaf (0)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (4)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (8)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (7))) (.branch 20 (.leaf (3)) (.leaf (6))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (4)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (8))) (.branch 28 (.leaf (5)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (1)))) (.branch 34 (.branch 33 (.leaf (4)) (.leaf (7))) (.branch 35 (.leaf (0)) (.leaf (6))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (1)))) (.branch 41 (.branch 40 (.leaf (8)) (.leaf (0))) (.branch 42 (.leaf (4)) (.leaf (5)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (1)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (7))) (.branch 49 (.leaf (4)) (.leaf (6))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (1)) (.leaf (2))) (.branch 53 (.leaf (0)) (.leaf (3)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (8))) (.branch 57 (.leaf (5)) (.leaf (4))))))))
  code := certificateP9_5572
  counts := ![(.branch 24 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 32 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.leaf (7))))),
  (.branch 33 (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-24)) (.leaf (-28)))),
  (.branch 26 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 55 (.leaf (-4)) (.leaf (-5)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-11)) (.leaf (-14)))) (.branch 37 (.leaf (-15)) (.branch 44 (.leaf (-16)) (.leaf (-17))))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-9)) (.leaf (-11)))),
  (.branch 33 (.branch 25 (.leaf (0)) (.leaf (-1))) (.branch 49 (.leaf (-2)) (.leaf (-4)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (-15)) (.leaf (-16)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-20)))),
  (.branch 11 (.leaf (0)) (.branch 40 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 54 (.branch 42 (.branch 36 (.leaf (-28)) (.leaf (-27))) (.branch 48 (.leaf (-26)) (.leaf (-25)))) (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 54 (.branch 45 (.leaf (-17)) (.branch 53 (.leaf (-16)) (.leaf (-14)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-10))) (.branch 57 (.leaf (-8)) (.leaf (-6))))),
  (.branch 56 (.branch 55 (.leaf (-11)) (.leaf (-9))) (.branch 57 (.leaf (-7)) (.leaf (-5)))),
  (.branch 50 (.leaf (-4)) (.branch 51 (.leaf (-2)) (.leaf (0)))),
  (.leaf (-2)),
  (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-14))) (.branch 53 (.leaf (-12)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-18))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-14)) (.leaf (-12))))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 41 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3))))]
def witnessP9_303_5573 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (1))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (7)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (6))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (3)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (8)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (5))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (3)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (6))) (.branch 28 (.leaf (7)) (.leaf (1))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 33 (.leaf (4)) (.leaf (1))) (.branch 35 (.leaf (5)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (8)) (.leaf (3)))) (.branch 41 (.branch 40 (.leaf (1)) (.leaf (6))) (.branch 42 (.leaf (0)) (.leaf (2)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (4)) (.branch 45 (.leaf (3)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (7)) (.leaf (0))) (.branch 49 (.leaf (2)) (.leaf (5))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (4)) (.leaf (1))) (.branch 53 (.leaf (3)) (.leaf (0)))) (.branch 56 (.branch 55 (.leaf (2)) (.leaf (6))) (.branch 57 (.leaf (8)) (.leaf (1))))))))
  code := certificateP9_5573
  counts := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 30 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-24))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 16 (.leaf (-10)) (.branch 45 (.leaf (-13)) (.leaf (-15))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 51 (.leaf (-19)) (.leaf (-24)))),
  (.branch 6 (.leaf (0)) (.leaf (-17))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (-31))) (.branch 47 (.leaf (-32)) (.leaf (-33)))),
  (.branch 18 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 49 (.branch 37 (.branch 31 (.leaf (-24)) (.leaf (-23))) (.branch 43 (.leaf (-22)) (.leaf (-21)))) (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 41 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.branch 53 (.leaf (-1)) (.leaf (0))))),
  (.branch 44 (.branch 32 (.leaf (-19)) (.branch 38 (.leaf (-18)) (.leaf (-17)))) (.branch 56 (.branch 50 (.leaf (-16)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 55 (.branch 46 (.leaf (-15)) (.branch 54 (.leaf (-14)) (.leaf (-12)))) (.branch 56 (.leaf (-10)) (.branch 57 (.leaf (-8)) (.leaf (-6))))),
  (.branch 54 (.branch 52 (.leaf (-24)) (.branch 53 (.leaf (-22)) (.leaf (-20)))) (.branch 56 (.branch 55 (.leaf (-18)) (.leaf (-16))) (.branch 57 (.leaf (-14)) (.leaf (-12))))),
  (.branch 53 (.branch 51 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-14)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 42 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 49 (.branch 48 (.leaf (-33)) (.leaf (-30))) (.branch 50 (.leaf (-27)) (.branch 51 (.leaf (-24)) (.leaf (-21))))) (.branch 55 (.branch 53 (.leaf (-18)) (.branch 54 (.leaf (-15)) (.leaf (-12)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 19 (.leaf (-4)) (.leaf (-3)))]
def witnessP9_303_5574 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (1))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (4)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (6))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (8)) (.branch 16 (.leaf (3)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (5))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (7)) (.leaf (1))) (.branch 24 (.leaf (3)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (6))) (.branch 28 (.leaf (4)) (.leaf (1))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 33 (.leaf (8)) (.leaf (1))) (.branch 35 (.leaf (5)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (4)) (.leaf (3)))) (.branch 41 (.branch 40 (.leaf (1)) (.leaf (6))) (.branch 42 (.leaf (0)) (.leaf (2)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (7)) (.branch 45 (.leaf (3)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (4)) (.leaf (0))) (.branch 49 (.leaf (2)) (.leaf (5))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (8)) (.leaf (1))) (.branch 53 (.leaf (3)) (.leaf (0)))) (.branch 56 (.branch 55 (.leaf (2)) (.leaf (6))) (.branch 57 (.leaf (4)) (.leaf (1))))))))
  code := certificateP9_5574
  counts := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 30 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-24))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 16 (.leaf (-10)) (.branch 45 (.leaf (-13)) (.leaf (-15))))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-2)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-17))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (-17)) (.leaf (-20)))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (-6))) (.branch 51 (.leaf (-9)) (.leaf (-12))))]
  high := ![(.branch 49 (.branch 37 (.branch 31 (.leaf (-24)) (.leaf (-23))) (.branch 43 (.leaf (-22)) (.leaf (-21)))) (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 41 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.branch 53 (.leaf (-1)) (.leaf (0))))),
  (.branch 44 (.branch 32 (.leaf (-19)) (.branch 38 (.leaf (-18)) (.leaf (-17)))) (.branch 56 (.branch 50 (.leaf (-16)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 55 (.branch 46 (.leaf (-15)) (.branch 54 (.leaf (-14)) (.leaf (-12)))) (.branch 56 (.leaf (-10)) (.branch 57 (.leaf (-8)) (.leaf (-6))))),
  (.branch 48 (.leaf (-4)) (.leaf (-3))),
  (.branch 53 (.branch 51 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-14)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 42 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-2)))),
  (.branch 50 (.branch 46 (.branch 23 (.leaf (-20)) (.branch 45 (.leaf (-19)) (.leaf (-18)))) (.branch 48 (.branch 47 (.leaf (-17)) (.leaf (-16))) (.branch 49 (.leaf (-15)) (.leaf (-14))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-13)) (.leaf (-12))) (.branch 53 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 54 (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6)))))]
def witnessP9_303_5575 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (1))) (.branch 6 (.leaf (8)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (2)) (.leaf (6)))) (.branch 12 (.branch 11 (.leaf (7)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (5)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (8)) (.leaf (4))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (6)) (.leaf (2))) (.branch 24 (.leaf (1)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (7)) (.leaf (3))) (.branch 28 (.leaf (5)) (.leaf (1))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (4)))) (.branch 34 (.branch 33 (.leaf (6)) (.leaf (1))) (.branch 35 (.leaf (8)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (2)) (.leaf (5)))) (.branch 41 (.branch 40 (.leaf (7)) (.leaf (1))) (.branch 42 (.leaf (0)) (.leaf (4)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (6)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (8)) (.leaf (4))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (5)) (.leaf (2))) (.branch 53 (.leaf (1)) (.leaf (0)))) (.branch 56 (.branch 55 (.leaf (7)) (.leaf (3))) (.branch 57 (.leaf (6)) (.leaf (1))))))))
  code := certificateP9_5575
  counts := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 30 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-24))),
  (.branch 5 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 15 (.leaf (-12)) (.branch 44 (.leaf (-15)) (.leaf (-17))))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-5)) (.leaf (-7)))),
  (.branch 21 (.branch 3 (.leaf (0)) (.leaf (-15))) (.branch 50 (.leaf (-21)) (.leaf (-26)))),
  (.branch 4 (.leaf (0)) (.leaf (-38))),
  (.branch 10 (.leaf (0)) (.branch 33 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18))))]
  high := ![(.branch 49 (.branch 37 (.branch 31 (.leaf (-24)) (.leaf (-23))) (.branch 43 (.leaf (-22)) (.leaf (-21)))) (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 35 (.leaf (-2)) (.branch 54 (.leaf (-1)) (.leaf (0)))),
  (.branch 54 (.branch 45 (.leaf (-17)) (.branch 53 (.leaf (-16)) (.leaf (-14)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-10))) (.branch 57 (.leaf (-8)) (.leaf (-6))))),
  (.branch 47 (.leaf (-7)) (.branch 57 (.leaf (-6)) (.leaf (-3)))),
  (.branch 54 (.branch 52 (.branch 51 (.leaf (-26)) (.leaf (-24))) (.branch 53 (.leaf (-22)) (.leaf (-20)))) (.branch 56 (.branch 55 (.leaf (-18)) (.leaf (-16))) (.branch 57 (.leaf (-14)) (.leaf (-12))))),
  (.branch 53 (.branch 40 (.branch 5 (.leaf (-38)) (.leaf (-37))) (.branch 52 (.leaf (-35)) (.leaf (-30)))) (.branch 55 (.branch 54 (.leaf (-25)) (.leaf (-20))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 34 (.leaf (-9)) (.branch 46 (.leaf (-7)) (.leaf (-5)))),
  (.branch 56 (.branch 41 (.leaf (-7)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2)))),
  (.branch 53 (.branch 51 (.branch 50 (.leaf (-18)) (.leaf (-16))) (.branch 52 (.leaf (-14)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2))))))]
def witnessP9_303_5576 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (8)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (6)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (7)) (.leaf (0))) (.branch 20 (.leaf (5)) (.leaf (2))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (8)))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (0))) (.branch 28 (.leaf (6)) (.leaf (1))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (5)))) (.branch 34 (.branch 33 (.leaf (7)) (.leaf (0))) (.branch 35 (.leaf (3)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (4)) (.leaf (8)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (6)) (.leaf (5)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (0)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (7)) (.leaf (0))) (.branch 49 (.leaf (4)) (.leaf (2))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (3)) (.leaf (8)))) (.branch 56 (.branch 55 (.leaf (5)) (.leaf (0))) (.branch 57 (.leaf (6)) (.leaf (1))))))))
  code := certificateP9_5576
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 29 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-21)) (.leaf (-23)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-23)) (.leaf (-25)))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (-9))) (.branch 53 (.leaf (-15)) (.leaf (-20)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-43)) (.leaf (-46)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (-13))) (.branch 43 (.leaf (-16)) (.leaf (-17)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (-21)) (.leaf (-22)))),
  (.branch 10 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 49 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 53 (.leaf (-19)) (.branch 57 (.leaf (-16)) (.leaf (-8))))),
  (.branch 37 (.leaf (-1)) (.leaf (0))),
  (.branch 53 (.branch 51 (.branch 41 (.leaf (-25)) (.leaf (-24))) (.branch 52 (.leaf (-21)) (.leaf (-18)))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 55 (.branch 54 (.leaf (-20)) (.leaf (-18))) (.branch 56 (.leaf (-16)) (.branch 57 (.leaf (-14)) (.leaf (-12))))),
  (.branch 53 (.branch 50 (.branch 15 (.leaf (-46)) (.leaf (-45))) (.branch 51 (.leaf (-40)) (.branch 52 (.leaf (-35)) (.leaf (-30))))) (.branch 55 (.branch 54 (.leaf (-25)) (.leaf (-20))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 56 (.branch 44 (.leaf (-17)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5)))),
  (.branch 43 (.leaf (-3)) (.leaf (-2))),
  (.branch 52 (.branch 49 (.branch 48 (.leaf (-22)) (.leaf (-20))) (.branch 50 (.leaf (-18)) (.branch 51 (.leaf (-16)) (.leaf (-14))))) (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-10)) (.leaf (-8)))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 55 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))]
def witnessP9_303_5577 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (2)) (.leaf (7))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (8)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (2))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (5)) (.leaf (0))) (.branch 24 (.leaf (6)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (7))) (.branch 28 (.leaf (4)) (.leaf (2))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (1)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (5))) (.branch 35 (.leaf (2)) (.leaf (8))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (6)) (.leaf (4)))) (.branch 41 (.branch 40 (.leaf (1)) (.leaf (0))) (.branch 42 (.leaf (3)) (.leaf (2)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (5)) (.leaf (7)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (3)) (.leaf (2))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (4)) (.leaf (0))) (.branch 53 (.leaf (6)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (8))) (.branch 57 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_5577
  counts := ![(.branch 26 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 33 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 55 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-21)) (.leaf (-26)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 6 (.leaf (0)) (.branch 35 (.leaf (-4)) (.leaf (-5)))),
  (.branch 20 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 49 (.leaf (-23)) (.leaf (-28)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-33))) (.branch 39 (.leaf (-36)) (.leaf (-37)))),
  (.branch 10 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.leaf (-37))),
  (.branch 17 (.leaf (0)) (.branch 36 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 45 (.branch 34 (.leaf (-26)) (.leaf (-25))) (.branch 56 (.leaf (-24)) (.branch 57 (.leaf (-16)) (.leaf (-8))))),
  (.branch 55 (.branch 33 (.leaf (-17)) (.leaf (-16))) (.branch 56 (.leaf (-12)) (.branch 57 (.leaf (-8)) (.leaf (-4))))),
  (.branch 51 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.branch 53 (.branch 51 (.branch 50 (.leaf (-28)) (.leaf (-26))) (.branch 52 (.leaf (-24)) (.leaf (-22)))) (.branch 55 (.branch 54 (.leaf (-20)) (.leaf (-18))) (.branch 56 (.leaf (-16)) (.branch 57 (.leaf (-14)) (.leaf (-12)))))),
  (.branch 54 (.branch 52 (.branch 40 (.leaf (-37)) (.leaf (-35))) (.branch 53 (.leaf (-30)) (.leaf (-25)))) (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 11 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-5)))),
  (.branch 55 (.branch 39 (.leaf (-11)) (.branch 54 (.leaf (-10)) (.leaf (-8)))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.branch 51 (.branch 48 (.branch 8 (.leaf (-37)) (.branch 47 (.leaf (-36)) (.leaf (-33)))) (.branch 49 (.leaf (-30)) (.branch 50 (.leaf (-27)) (.leaf (-24))))) (.branch 54 (.branch 52 (.leaf (-21)) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 37 (.leaf (-8)) (.branch 57 (.leaf (-6)) (.leaf (-3))))]
def witnessP9_303_5578 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (7))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (8)) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (1)) (.leaf (4))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (7)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (4))) (.branch 28 (.leaf (2)) (.leaf (5))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (1)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (8))) (.branch 35 (.leaf (0)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (3)) (.leaf (6)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (4)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (7)) (.branch 45 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (5))) (.branch 49 (.leaf (1)) (.leaf (4))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (2)) (.leaf (3))) (.branch 53 (.leaf (0)) (.leaf (8)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (4))) (.branch 57 (.leaf (2)) (.leaf (6))))))))
  code := certificateP9_5578
  counts := ![(.branch 24 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 32 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 33 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-24)) (.leaf (-28)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.branch 33 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-16))) (.branch 23 (.leaf (-17)) (.branch 52 (.leaf (-19)) (.leaf (-20))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-1)) (.leaf (-3)))) (.branch 42 (.leaf (-5)) (.branch 56 (.leaf (-6)) (.leaf (-8))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (-28))) (.branch 48 (.leaf (-29)) (.leaf (-30)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-43))),
  (.branch 15 (.leaf (0)) (.branch 34 (.leaf (-13)) (.leaf (-14))))]
  high := ![(.branch 54 (.branch 42 (.branch 36 (.leaf (-28)) (.leaf (-27))) (.branch 48 (.leaf (-26)) (.leaf (-25)))) (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 50 (.branch 38 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-3)),
  (.branch 55 (.branch 53 (.leaf (-20)) (.branch 54 (.leaf (-17)) (.leaf (-14)))) (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-8)) (.leaf (-5))))),
  (.branch 57 (.leaf (-8)) (.leaf (-7))),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-30)) (.leaf (-27))) (.branch 51 (.leaf (-24)) (.branch 52 (.leaf (-21)) (.leaf (-18))))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 50 (.branch 46 (.branch 6 (.leaf (-43)) (.branch 45 (.leaf (-42)) (.leaf (-39)))) (.branch 48 (.branch 47 (.leaf (-36)) (.leaf (-33))) (.branch 49 (.leaf (-30)) (.leaf (-27))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-24)) (.leaf (-21))) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 55 (.branch 35 (.leaf (-14)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))]
def witnessP9_303_5579 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (2))) (.branch 6 (.leaf (8)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (6)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (3)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (3)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (5)) (.leaf (4))) (.branch 28 (.leaf (1)) (.leaf (2))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (6)))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (2))) (.branch 35 (.leaf (8)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (5)) (.leaf (3)))) (.branch 41 (.branch 40 (.leaf (1)) (.leaf (2))) (.branch 42 (.leaf (0)) (.leaf (6)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (3)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (4)) (.leaf (0))) (.branch 49 (.leaf (5)) (.leaf (7))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (1)) (.leaf (2))) (.branch 53 (.leaf (3)) (.leaf (0)))) (.branch 56 (.branch 55 (.leaf (6)) (.leaf (4))) (.branch 57 (.leaf (1)) (.leaf (2))))))))
  code := certificateP9_5579
  counts := ![(.branch 25 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 30 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 33 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-24))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 44 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-16))) (.branch 45 (.leaf (-18)) (.leaf (-19)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-43)) (.leaf (-46)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (-13))) (.branch 43 (.leaf (-16)) (.leaf (-17)))),
  (.branch 21 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.leaf (-23)))]
  high := ![(.branch 49 (.branch 37 (.branch 31 (.leaf (-24)) (.leaf (-23))) (.branch 43 (.leaf (-22)) (.leaf (-21)))) (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 45 (.leaf (-4)) (.leaf (-3))),
  (.branch 53 (.leaf (-2)) (.branch 54 (.leaf (-1)) (.leaf (0)))),
  (.branch 55 (.branch 46 (.leaf (-19)) (.branch 54 (.leaf (-17)) (.leaf (-14)))) (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-8)) (.leaf (-5))))),
  (.branch 57 (.leaf (-6)) (.leaf (-3))),
  (.branch 53 (.branch 50 (.branch 15 (.leaf (-46)) (.leaf (-45))) (.branch 51 (.leaf (-40)) (.branch 52 (.leaf (-35)) (.leaf (-30))))) (.branch 55 (.branch 54 (.leaf (-25)) (.leaf (-20))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 56 (.branch 44 (.leaf (-17)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5)))),
  (.branch 54 (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 40 (.branch 37 (.branch 36 (.leaf (-23)) (.leaf (-22))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-20)) (.leaf (-19))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))))) (.branch 52 (.branch 49 (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_303_5580 : CycleWitness 9 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (7)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (6)) (.leaf (3))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (5)) (.leaf (0))) (.branch 28 (.leaf (8)) (.leaf (1))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (6)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (0))) (.branch 35 (.leaf (4)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (3)) (.leaf (0))) (.branch 42 (.leaf (7)) (.leaf (6)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (0)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (5)) (.leaf (3))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (4)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (6)) (.leaf (0))) (.branch 57 (.leaf (8)) (.leaf (1))))))))
  code := certificateP9_5580
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 29 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 57 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-21)) (.leaf (-23)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 39 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-23)) (.leaf (-25)))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (-9))) (.branch 53 (.leaf (-15)) (.leaf (-20)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-43)) (.leaf (-46)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (-13))) (.branch 43 (.leaf (-16)) (.leaf (-17)))),
  (.branch 13 (.leaf (0)) (.leaf (-16))),
  (.branch 28 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 49 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 53 (.leaf (-19)) (.branch 57 (.leaf (-16)) (.leaf (-8))))),
  (.branch 37 (.leaf (-1)) (.leaf (0))),
  (.branch 55 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-8)) (.leaf (-5))))),
  (.branch 53 (.branch 51 (.branch 41 (.leaf (-25)) (.leaf (-24))) (.branch 52 (.leaf (-21)) (.leaf (-18)))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 55 (.branch 54 (.leaf (-20)) (.leaf (-18))) (.branch 56 (.leaf (-16)) (.branch 57 (.leaf (-14)) (.leaf (-12))))),
  (.branch 53 (.branch 50 (.branch 15 (.leaf (-46)) (.leaf (-45))) (.branch 51 (.leaf (-40)) (.branch 52 (.leaf (-35)) (.leaf (-30))))) (.branch 55 (.branch 54 (.leaf (-25)) (.leaf (-20))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 56 (.branch 44 (.leaf (-17)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5)))),
  (.branch 50 (.branch 46 (.branch 44 (.branch 43 (.leaf (-16)) (.leaf (-15))) (.branch 45 (.leaf (-14)) (.leaf (-13)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-11))) (.branch 49 (.leaf (-10)) (.leaf (-9))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_303_5581 : CycleWitness 9 where
  length := 57
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (1)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (4)))))) (.branch 22 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (6))) (.branch 21 (.leaf (0)) (.leaf (2))))) (.branch 25 (.branch 23 (.leaf (1)) (.branch 24 (.leaf (0)) (.leaf (4)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (5)) (.leaf (0))))))) (.branch 43 (.branch 35 (.branch 32 (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (2)))) (.branch 33 (.leaf (4)) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (7)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (2))) (.branch 42 (.leaf (1)) (.leaf (0)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (4)) (.branch 45 (.leaf (0)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (5)) (.leaf (0))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 53 (.branch 51 (.leaf (2)) (.branch 52 (.leaf (4)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (0))) (.branch 56 (.leaf (3)) (.leaf (8))))))))
  code := certificateP9_5581
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 24 (.leaf (10)) (.leaf (11)))))) (.branch 40 (.branch 34 (.branch 29 (.leaf (12)) (.branch 31 (.leaf (13)) (.leaf (14)))) (.branch 36 (.leaf (15)) (.branch 39 (.leaf (16)) (.leaf (17))))) (.branch 48 (.branch 43 (.leaf (18)) (.branch 45 (.leaf (19)) (.leaf (20)))) (.branch 53 (.branch 50 (.leaf (21)) (.leaf (22))) (.branch 55 (.leaf (23)) (.leaf (24))))))),
  (.branch 30 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1))),
  (.branch 57 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 21 (.leaf (-20)) (.branch 40 (.leaf (-23)) (.leaf (-26))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 35 (.leaf (-7)) (.branch 54 (.leaf (-8)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 33 (.leaf (-6)) (.branch 52 (.leaf (-7)) (.leaf (-8))))),
  (.branch 9 (.leaf (0)) (.leaf (-10))),
  (.branch 19 (.leaf (0)) (.leaf (-38))),
  (.branch 38 (.leaf (0)) (.leaf (-19))),
  (.leaf (0))]
  high := ![(.branch 46 (.branch 41 (.leaf (-26)) (.leaf (-25))) (.branch 51 (.leaf (-24)) (.branch 56 (.leaf (-23)) (.leaf (-16))))),
  (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-7)) (.leaf (-5)))),
  (.branch 53 (.branch 42 (.leaf (-13)) (.branch 52 (.leaf (-12)) (.leaf (-10)))) (.branch 55 (.branch 54 (.leaf (-8)) (.leaf (-6))) (.branch 56 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.leaf (-3)) (.leaf (-2))),
  (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4))))),
  (.branch 52 (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-7)) (.leaf (-6))))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (-38)) (.leaf (-37))) (.branch 22 (.leaf (-36)) (.leaf (-35)))) (.branch 25 (.branch 24 (.leaf (-34)) (.leaf (-33))) (.branch 26 (.leaf (-32)) (.branch 27 (.leaf (-31)) (.leaf (-30)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-29)) (.leaf (-28))) (.branch 31 (.leaf (-27)) (.branch 32 (.leaf (-26)) (.leaf (-25))))) (.branch 35 (.branch 34 (.leaf (-24)) (.leaf (-23))) (.branch 36 (.leaf (-22)) (.branch 37 (.leaf (-21)) (.leaf (-20))))))) (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-19)) (.leaf (-18))) (.branch 41 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-7)) (.leaf (-6))))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-19)) (.leaf (-18))) (.branch 41 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-7)) (.leaf (-6))))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_303_5582 : CycleWitness 9 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (7)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (8)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (7)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (5)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (8))) (.branch 34 (.leaf (2)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (6)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (5)) (.branch 44 (.leaf (7)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (2))) (.branch 48 (.leaf (3)) (.leaf (1))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (4))) (.branch 52 (.leaf (8)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (0))) (.branch 56 (.leaf (6)) (.leaf (5))))))))
  code := certificateP9_5582
  counts := ![(.branch 27 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 36 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.leaf (15)))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 37 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 23 (.leaf (-4)) (.branch 42 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (-10))) (.branch 32 (.leaf (-11)) (.leaf (-13)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (-5))) (.branch 38 (.leaf (-6)) (.branch 51 (.leaf (-7)) (.leaf (-9))))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 18 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 51 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))),
  (.branch 55 (.branch 50 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-8)) (.leaf (-4)))),
  (.branch 55 (.branch 54 (.leaf (-12)) (.leaf (-9))) (.branch 56 (.leaf (-6)) (.leaf (-3)))),
  (.branch 52 (.branch 49 (.branch 33 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 54 (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7)))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4))))),
  (.branch 44 (.leaf (-2)) (.branch 45 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 50 (.branch 47 (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))) (.branch 48 (.leaf (-10)) (.branch 49 (.leaf (-9)) (.leaf (-8))))) (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_303_5583 : CycleWitness 9 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (5)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (7)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (5)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (4)) (.branch 44 (.leaf (8)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (2))) (.branch 48 (.leaf (3)) (.leaf (0))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (1)) (.leaf (2))) (.branch 52 (.leaf (0)) (.leaf (5)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (0))) (.branch 56 (.leaf (2)) (.leaf (3))))))))
  code := certificateP9_5583
  counts := ![(.branch 27 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))) (.branch 42 (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.branch 39 (.leaf (12)) (.leaf (13))))) (.branch 49 (.branch 46 (.leaf (14)) (.leaf (15))) (.branch 52 (.leaf (16)) (.branch 55 (.leaf (17)) (.leaf (18))))))),
  (.branch 26 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 13 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 22 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 41 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-14))),
  (.branch 15 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-51))),
  (.branch 25 (.leaf (0)) (.leaf (-32))),
  (.branch 44 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 43 (.leaf (-14)) (.branch 56 (.leaf (-12)) (.leaf (-6)))),
  (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-4)),
  (.leaf (0)),
  (.branch 50 (.branch 46 (.branch 44 (.leaf (-14)) (.branch 45 (.leaf (-13)) (.leaf (-12)))) (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.leaf (-8))))) (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 18 (.branch 12 (.branch 9 (.branch 7 (.leaf (-51)) (.branch 8 (.leaf (-50)) (.leaf (-49)))) (.branch 10 (.leaf (-48)) (.branch 11 (.leaf (-47)) (.leaf (-46))))) (.branch 15 (.branch 13 (.leaf (-45)) (.branch 14 (.leaf (-44)) (.leaf (-43)))) (.branch 16 (.leaf (-42)) (.branch 17 (.leaf (-41)) (.leaf (-40)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-39)) (.branch 20 (.leaf (-38)) (.leaf (-37)))) (.branch 22 (.leaf (-36)) (.branch 23 (.leaf (-35)) (.leaf (-34))))) (.branch 27 (.branch 25 (.leaf (-33)) (.branch 26 (.leaf (-32)) (.leaf (-31)))) (.branch 29 (.branch 28 (.leaf (-30)) (.leaf (-29))) (.branch 30 (.leaf (-28)) (.leaf (-27))))))) (.branch 44 (.branch 37 (.branch 34 (.branch 32 (.leaf (-26)) (.branch 33 (.leaf (-25)) (.leaf (-24)))) (.branch 35 (.leaf (-23)) (.branch 36 (.leaf (-22)) (.leaf (-21))))) (.branch 40 (.branch 38 (.leaf (-20)) (.branch 39 (.leaf (-19)) (.leaf (-18)))) (.branch 42 (.branch 41 (.leaf (-17)) (.leaf (-16))) (.branch 43 (.leaf (-15)) (.leaf (-14)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))) (.branch 48 (.leaf (-10)) (.branch 49 (.leaf (-9)) (.leaf (-8))))) (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-32)) (.leaf (-31))) (.branch 28 (.leaf (-30)) (.leaf (-29)))) (.branch 31 (.branch 30 (.leaf (-28)) (.leaf (-27))) (.branch 32 (.leaf (-26)) (.leaf (-25))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-24)) (.leaf (-23))) (.branch 36 (.leaf (-22)) (.leaf (-21)))) (.branch 39 (.branch 38 (.leaf (-20)) (.leaf (-19))) (.branch 40 (.leaf (-18)) (.leaf (-17)))))) (.branch 49 (.branch 45 (.branch 43 (.branch 42 (.leaf (-16)) (.leaf (-15))) (.branch 44 (.leaf (-14)) (.leaf (-13)))) (.branch 47 (.branch 46 (.leaf (-12)) (.leaf (-11))) (.branch 48 (.leaf (-10)) (.leaf (-9))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 47 (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))) (.branch 48 (.leaf (-10)) (.branch 49 (.leaf (-9)) (.leaf (-8))))) (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_303_5584 : CycleWitness 9 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (5)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (3)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (5)) (.leaf (4))) (.branch 34 (.leaf (2)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (7)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (5)) (.branch 44 (.leaf (4)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (2))) (.branch 48 (.leaf (3)) (.leaf (1))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (5))) (.branch 52 (.leaf (4)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (0))) (.branch 56 (.leaf (8)) (.leaf (3))))))))
  code := certificateP9_5584
  counts := ![(.branch 27 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 36 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.leaf (15)))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 23 (.leaf (-4)) (.branch 42 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 33 (.leaf (-6)) (.branch 52 (.leaf (-7)) (.leaf (-8))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 32 (.leaf (-7)) (.branch 51 (.leaf (-8)) (.leaf (-9))))),
  (.branch 18 (.leaf (0)) (.leaf (-39))),
  (.branch 37 (.leaf (0)) (.leaf (-20))),
  (.branch 56 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 51 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))),
  (.branch 55 (.branch 50 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-8)) (.leaf (-4)))),
  (.branch 55 (.branch 54 (.leaf (-12)) (.leaf (-9))) (.branch 56 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4))))),
  (.branch 54 (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7)))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4))))),
  (.branch 37 (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (-39)) (.leaf (-38))) (.branch 21 (.leaf (-37)) (.leaf (-36)))) (.branch 24 (.branch 23 (.leaf (-35)) (.leaf (-34))) (.branch 25 (.leaf (-33)) (.branch 26 (.leaf (-32)) (.leaf (-31)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (-30)) (.leaf (-29))) (.branch 30 (.leaf (-28)) (.branch 31 (.leaf (-27)) (.leaf (-26))))) (.branch 34 (.branch 33 (.leaf (-25)) (.leaf (-24))) (.branch 35 (.leaf (-23)) (.branch 36 (.leaf (-22)) (.leaf (-21))))))) (.branch 47 (.branch 42 (.branch 39 (.branch 38 (.leaf (-20)) (.leaf (-19))) (.branch 40 (.leaf (-18)) (.branch 41 (.leaf (-17)) (.leaf (-16))))) (.branch 44 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-7)) (.leaf (-6))))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 42 (.branch 39 (.branch 38 (.leaf (-20)) (.leaf (-19))) (.branch 40 (.leaf (-18)) (.branch 41 (.leaf (-17)) (.leaf (-16))))) (.branch 44 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-7)) (.leaf (-6))))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_303_5585 : CycleWitness 9 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (6))) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (7)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (8)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (6))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (4)) (.branch 23 (.leaf (0)) (.leaf (7)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (5)) (.leaf (0))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (8)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (6))) (.branch 34 (.leaf (2)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (4)) (.leaf (7)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (5)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (8)) (.branch 44 (.leaf (2)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (0))) (.branch 48 (.leaf (6)) (.leaf (1))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (4))) (.branch 52 (.leaf (7)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (0))) (.branch 56 (.leaf (5)) (.leaf (8))))))))
  code := certificateP9_5585
  counts := ![(.branch 28 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 36 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.leaf (15)))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 23 (.leaf (-4)) (.branch 42 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-45))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (-25)) (.leaf (-26)))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (-5))) (.branch 41 (.leaf (-6)) (.leaf (-7)))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (-37))) (.branch 33 (.leaf (-38)) (.leaf (-39)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (-17))) (.branch 38 (.leaf (-18)) (.branch 52 (.leaf (-19)) (.leaf (-20))))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 51 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))),
  (.branch 55 (.branch 50 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-8)) (.leaf (-4)))),
  (.branch 55 (.branch 54 (.leaf (-8)) (.leaf (-6))) (.branch 56 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.branch 48 (.branch 4 (.leaf (-45)) (.branch 47 (.leaf (-44)) (.leaf (-40)))) (.branch 49 (.leaf (-36)) (.branch 50 (.leaf (-32)) (.leaf (-28))))) (.branch 54 (.branch 52 (.leaf (-24)) (.branch 53 (.leaf (-20)) (.leaf (-16)))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 53 (.branch 23 (.leaf (-26)) (.branch 52 (.leaf (-24)) (.leaf (-20)))) (.branch 55 (.branch 54 (.leaf (-16)) (.leaf (-12))) (.branch 56 (.leaf (-8)) (.leaf (-4))))),
  (.branch 42 (.leaf (-7)) (.leaf (-4))),
  (.branch 52 (.branch 49 (.branch 34 (.leaf (-39)) (.leaf (-36))) (.branch 50 (.leaf (-32)) (.branch 51 (.leaf (-28)) (.leaf (-24))))) (.branch 54 (.branch 53 (.leaf (-20)) (.leaf (-16))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 54 (.branch 53 (.leaf (-20)) (.leaf (-16))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4))))),
  (.branch 15 (.leaf (-1)) (.leaf (0)))]
def witnessP9_303_5586 : CycleWitness 9 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (8))) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (1)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (7)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (5)) (.branch 23 (.leaf (0)) (.leaf (8)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (4)) (.branch 30 (.leaf (0)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (5))) (.branch 34 (.leaf (7)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (4)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (8)) (.branch 44 (.leaf (5)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (6)) (.leaf (1))) (.branch 48 (.leaf (3)) (.leaf (0))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (4)) (.leaf (7)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (0))) (.branch 56 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_5586
  counts := ![(.branch 26 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))) (.branch 42 (.branch 32 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.branch 39 (.leaf (12)) (.leaf (13))))) (.branch 49 (.branch 45 (.leaf (14)) (.leaf (15))) (.branch 51 (.leaf (16)) (.branch 55 (.leaf (17)) (.leaf (18))))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 12 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 48 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 32 (.branch 13 (.leaf (-13)) (.leaf (-15))) (.branch 51 (.leaf (-16)) (.leaf (-17))))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 40 (.leaf (-10)) (.leaf (-11)))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (-3)) (.leaf (-6)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-42))) (.branch 25 (.leaf (-44)) (.leaf (-46)))),
  (.branch 6 (.leaf (0)) (.leaf (-27))),
  (.branch 10 (.leaf (0)) (.branch 44 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 52 (.leaf (-17)) (.branch 56 (.leaf (-13)) (.leaf (-8)))),
  (.branch 48 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-7)) (.leaf (-5))))),
  (.branch 52 (.branch 39 (.leaf (-6)) (.branch 51 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.branch 53 (.leaf (-3)) (.leaf (-2))) (.branch 55 (.leaf (-1)) (.leaf (0))))),
  (.branch 52 (.branch 49 (.branch 26 (.leaf (-46)) (.leaf (-45))) (.branch 50 (.leaf (-40)) (.branch 51 (.leaf (-35)) (.leaf (-30))))) (.branch 54 (.branch 53 (.leaf (-25)) (.leaf (-20))) (.branch 55 (.leaf (-15)) (.branch 56 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 53 (.branch 7 (.leaf (-27)) (.branch 30 (.leaf (-26)) (.leaf (-25)))) (.branch 55 (.branch 54 (.leaf (-20)) (.leaf (-15))) (.branch 56 (.leaf (-10)) (.leaf (-5))))),
  (.branch 45 (.leaf (-8)) (.leaf (-5))),
  (.branch 51 (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 54 (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1)))),
  (.branch 50 (.branch 46 (.branch 44 (.leaf (-14)) (.branch 45 (.leaf (-13)) (.leaf (-12)))) (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.leaf (-8))))) (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_303_5587 : CycleWitness 9 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (4))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (5)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (1)) (.leaf (3))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (2)) (.leaf (4)))) (.branch 33 (.branch 32 (.leaf (5)) (.leaf (1))) (.branch 34 (.leaf (0)) (.leaf (3))))) (.branch 38 (.branch 36 (.leaf (2)) (.branch 37 (.leaf (7)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (3)) (.leaf (5)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (4)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (3))) (.branch 48 (.leaf (0)) (.leaf (2))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (2))) (.branch 56 (.leaf (8)) (.leaf (4))))))))
  code := certificateP9_5587
  counts := ![(.branch 25 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 46 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 30 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 50 (.leaf (7)) (.branch 57 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-15)) (.leaf (-17)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-10)) (.leaf (-11)))),
  (.branch 31 (.branch 12 (.leaf (0)) (.leaf (-2))) (.branch 50 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 18 (.leaf (0)) (.leaf (-39))),
  (.branch 37 (.leaf (0)) (.leaf (-20))),
  (.branch 56 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 54 (.branch 49 (.leaf (-17)) (.leaf (-16))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4))))),
  (.branch 54 (.branch 53 (.leaf (-15)) (.leaf (-12))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-6)) (.leaf (-3))))),
  (.branch 56 (.leaf (-6)) (.leaf (-3))),
  (.branch 55 (.branch 48 (.leaf (-11)) (.leaf (-9))) (.branch 56 (.leaf (-6)) (.leaf (-3)))),
  (.branch 51 (.leaf (-4)) (.branch 52 (.leaf (-2)) (.leaf (0)))),
  (.branch 54 (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-10)) (.leaf (-8)))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-4)) (.leaf (-2))))),
  (.branch 37 (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (-39)) (.leaf (-38))) (.branch 21 (.leaf (-37)) (.leaf (-36)))) (.branch 24 (.branch 23 (.leaf (-35)) (.leaf (-34))) (.branch 25 (.leaf (-33)) (.branch 26 (.leaf (-32)) (.leaf (-31)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (-30)) (.leaf (-29))) (.branch 30 (.leaf (-28)) (.branch 31 (.leaf (-27)) (.leaf (-26))))) (.branch 34 (.branch 33 (.leaf (-25)) (.leaf (-24))) (.branch 35 (.leaf (-23)) (.branch 36 (.leaf (-22)) (.leaf (-21))))))) (.branch 47 (.branch 42 (.branch 39 (.branch 38 (.leaf (-20)) (.leaf (-19))) (.branch 40 (.leaf (-18)) (.branch 41 (.leaf (-17)) (.leaf (-16))))) (.branch 44 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-7)) (.leaf (-6))))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 42 (.branch 39 (.branch 38 (.leaf (-20)) (.leaf (-19))) (.branch 40 (.leaf (-18)) (.branch 41 (.leaf (-17)) (.leaf (-16))))) (.branch 44 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-7)) (.leaf (-6))))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_303_5588 : CycleWitness 9 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (7)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (5))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (8)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (0))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (4)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (6))) (.branch 34 (.leaf (3)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (3)) (.leaf (7)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (0))) (.branch 48 (.leaf (4)) (.leaf (1))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (8)) (.leaf (3)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (0))) (.branch 56 (.leaf (2)) (.leaf (5))))))))
  code := certificateP9_5588
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.leaf (15)))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 37 (.leaf (5)) (.leaf (6))) (.branch 50 (.leaf (7)) (.branch 56 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 46 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 27 (.leaf (-10)) (.branch 46 (.leaf (-11)) (.leaf (-12))))),
  (.branch 10 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-49))),
  (.branch 14 (.leaf (0)) (.branch 42 (.leaf (-29)) (.leaf (-30)))),
  (.branch 23 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 48 (.branch 40 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 52 (.leaf (-11)) (.branch 56 (.leaf (-10)) (.leaf (-5))))),
  (.branch 55 (.branch 50 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-3)),
  (.branch 54 (.branch 47 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-7)) (.leaf (-5))))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 51 (.leaf (-7)) (.leaf (-6)))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 44 (.branch 38 (.branch 35 (.branch 5 (.leaf (-49)) (.branch 34 (.leaf (-48)) (.leaf (-46)))) (.branch 36 (.leaf (-44)) (.branch 37 (.leaf (-42)) (.leaf (-40))))) (.branch 41 (.branch 39 (.leaf (-38)) (.branch 40 (.leaf (-36)) (.leaf (-34)))) (.branch 42 (.leaf (-32)) (.branch 43 (.leaf (-30)) (.leaf (-28)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-26)) (.branch 46 (.leaf (-24)) (.leaf (-22)))) (.branch 48 (.leaf (-20)) (.branch 49 (.leaf (-18)) (.leaf (-16))))) (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-12)) (.leaf (-10)))) (.branch 55 (.branch 54 (.leaf (-8)) (.leaf (-6))) (.branch 56 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 49 (.branch 45 (.branch 43 (.leaf (-30)) (.branch 44 (.leaf (-28)) (.leaf (-26)))) (.branch 47 (.branch 46 (.leaf (-24)) (.leaf (-22))) (.branch 48 (.leaf (-20)) (.leaf (-18))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-16)) (.leaf (-14))) (.branch 52 (.leaf (-12)) (.leaf (-10)))) (.branch 55 (.branch 54 (.leaf (-8)) (.leaf (-6))) (.branch 56 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 54 (.branch 24 (.leaf (-11)) (.branch 53 (.leaf (-10)) (.leaf (-8)))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-4)) (.leaf (-2)))))]
def witnessP9_303_5589 : CycleWitness 9 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (4)) (.branch 23 (.leaf (0)) (.leaf (3)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (4)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (7))) (.branch 34 (.leaf (3)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (5)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (4)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (5)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (1))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (4)) (.leaf (0))) (.branch 52 (.leaf (8)) (.leaf (3)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (0))) (.branch 56 (.leaf (5)) (.leaf (2))))))))
  code := certificateP9_5589
  counts := ![(.branch 26 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))) (.branch 42 (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.branch 39 (.leaf (12)) (.leaf (13))))) (.branch 48 (.branch 45 (.leaf (14)) (.leaf (15))) (.branch 51 (.leaf (16)) (.branch 55 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-14)))) (.branch 10 (.leaf (-15)) (.branch 13 (.leaf (-16)) (.leaf (-17))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-43))),
  (.branch 33 (.leaf (0)) (.leaf (-24))),
  (.branch 52 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 52 (.leaf (-17)) (.branch 56 (.leaf (-12)) (.leaf (-6)))),
  (.branch 50 (.branch 45 (.leaf (-14)) (.leaf (-13))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4))))),
  (.branch 48 (.leaf (-1)) (.leaf (0))),
  (.branch 54 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-4)) (.leaf (-2))))),
  (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-12)) (.leaf (-10)))) (.branch 55 (.branch 54 (.leaf (-8)) (.leaf (-6))) (.branch 56 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.leaf (-3)) (.leaf (-2))),
  (.branch 35 (.branch 24 (.branch 19 (.branch 16 (.branch 15 (.leaf (-43)) (.leaf (-42))) (.branch 17 (.leaf (-41)) (.branch 18 (.leaf (-40)) (.leaf (-39))))) (.branch 21 (.branch 20 (.leaf (-38)) (.leaf (-37))) (.branch 22 (.leaf (-36)) (.branch 23 (.leaf (-35)) (.leaf (-34)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-33)) (.leaf (-32))) (.branch 27 (.leaf (-31)) (.branch 28 (.leaf (-30)) (.leaf (-29))))) (.branch 32 (.branch 30 (.leaf (-28)) (.branch 31 (.leaf (-27)) (.leaf (-26)))) (.branch 33 (.leaf (-25)) (.branch 34 (.leaf (-24)) (.leaf (-23))))))) (.branch 46 (.branch 40 (.branch 37 (.branch 36 (.leaf (-22)) (.leaf (-21))) (.branch 38 (.leaf (-20)) (.branch 39 (.leaf (-19)) (.leaf (-18))))) (.branch 43 (.branch 41 (.leaf (-17)) (.branch 42 (.leaf (-16)) (.leaf (-15)))) (.branch 44 (.leaf (-14)) (.branch 45 (.leaf (-13)) (.leaf (-12)))))) (.branch 51 (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 54 (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 45 (.branch 39 (.branch 36 (.branch 34 (.leaf (-24)) (.branch 35 (.leaf (-23)) (.leaf (-22)))) (.branch 37 (.leaf (-21)) (.branch 38 (.leaf (-20)) (.leaf (-19))))) (.branch 42 (.branch 40 (.leaf (-18)) (.branch 41 (.leaf (-17)) (.leaf (-16)))) (.branch 43 (.leaf (-15)) (.branch 44 (.leaf (-14)) (.leaf (-13)))))) (.branch 51 (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-11)) (.leaf (-10)))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 54 (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_303_5590 : CycleWitness 9 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (4))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (5)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (0))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (4)) (.branch 30 (.leaf (5)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (3)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (7)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (1)) (.leaf (5)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (0))) (.branch 48 (.leaf (4)) (.leaf (5))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (1)) (.leaf (0))) (.branch 52 (.leaf (2)) (.leaf (3)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (0))) (.branch 56 (.leaf (8)) (.leaf (4))))))))
  code := certificateP9_5590
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.leaf (15)))))),
  (.branch 26 (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 46 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-2)) (.leaf (-3)))) (.branch 35 (.leaf (-4)) (.branch 54 (.leaf (-5)) (.leaf (-6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 30 (.leaf (-11)) (.branch 49 (.leaf (-14)) (.leaf (-17))))),
  (.branch 18 (.leaf (0)) (.leaf (-39))),
  (.branch 37 (.leaf (0)) (.leaf (-20))),
  (.branch 56 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 48 (.branch 40 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 52 (.leaf (-11)) (.branch 56 (.leaf (-10)) (.leaf (-5))))),
  (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))),
  (.branch 54 (.branch 53 (.leaf (-15)) (.leaf (-12))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-6)) (.leaf (-3))))),
  (.branch 55 (.branch 54 (.leaf (-8)) (.leaf (-6))) (.branch 56 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 53 (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))) (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.leaf (-10))))),
  (.branch 37 (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (-39)) (.leaf (-38))) (.branch 21 (.leaf (-37)) (.leaf (-36)))) (.branch 24 (.branch 23 (.leaf (-35)) (.leaf (-34))) (.branch 25 (.leaf (-33)) (.branch 26 (.leaf (-32)) (.leaf (-31)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (-30)) (.leaf (-29))) (.branch 30 (.leaf (-28)) (.branch 31 (.leaf (-27)) (.leaf (-26))))) (.branch 34 (.branch 33 (.leaf (-25)) (.leaf (-24))) (.branch 35 (.leaf (-23)) (.branch 36 (.leaf (-22)) (.leaf (-21))))))) (.branch 47 (.branch 42 (.branch 39 (.branch 38 (.leaf (-20)) (.leaf (-19))) (.branch 40 (.leaf (-18)) (.branch 41 (.leaf (-17)) (.leaf (-16))))) (.branch 44 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-7)) (.leaf (-6))))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 42 (.branch 39 (.branch 38 (.leaf (-20)) (.leaf (-19))) (.branch 40 (.leaf (-18)) (.branch 41 (.leaf (-17)) (.leaf (-16))))) (.branch 44 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-7)) (.leaf (-6))))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_303_5591 : CycleWitness 9 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (8)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (5))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (7)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (4)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (6)) (.branch 30 (.leaf (0)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (8)) (.leaf (3))) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (5)) (.branch 37 (.leaf (4)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (3))) (.branch 41 (.leaf (1)) (.leaf (7)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (6)) (.branch 44 (.leaf (0)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (4)) (.leaf (1))) (.branch 48 (.leaf (3)) (.leaf (0))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (8))) (.branch 52 (.leaf (2)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (3))) (.branch 56 (.leaf (4)) (.leaf (6))))))))
  code := certificateP9_5591
  counts := ![(.branch 25 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-15))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-41))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-17)) (.leaf (-18)))) (.branch 33 (.branch 26 (.leaf (-19)) (.leaf (-20))) (.branch 40 (.leaf (-21)) (.leaf (-22))))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (-29)) (.leaf (-30)))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 50 (.branch 40 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4))))),
  (.branch 55 (.branch 54 (.leaf (-12)) (.leaf (-9))) (.branch 56 (.leaf (-6)) (.leaf (-3)))),
  (.branch 54 (.branch 3 (.leaf (-41)) (.branch 53 (.leaf (-40)) (.leaf (-32)))) (.branch 55 (.leaf (-24)) (.branch 56 (.leaf (-16)) (.leaf (-8))))),
  (.branch 41 (.leaf (-22)) (.branch 56 (.leaf (-16)) (.leaf (-8)))),
  (.branch 47 (.leaf (-3)) (.leaf (-2))),
  (.branch 53 (.branch 51 (.branch 22 (.leaf (-30)) (.leaf (-28))) (.branch 52 (.leaf (-24)) (.leaf (-20)))) (.branch 55 (.branch 54 (.leaf (-16)) (.leaf (-12))) (.branch 56 (.leaf (-8)) (.leaf (-4))))),
  (.branch 15 (.leaf (-1)) (.leaf (0))),
  (.branch 49 (.branch 45 (.branch 43 (.leaf (-15)) (.branch 44 (.leaf (-14)) (.leaf (-13)))) (.branch 47 (.branch 46 (.leaf (-12)) (.leaf (-11))) (.branch 48 (.leaf (-10)) (.leaf (-9))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_303_5592 : CycleWitness 9 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (1)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (5))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (7))) (.branch 27 (.leaf (1)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (5)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (4))) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (3)) (.branch 37 (.leaf (1)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (3)) (.leaf (1)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (4)) (.branch 44 (.leaf (0)) (.leaf (8)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (2))) (.branch 48 (.leaf (3)) (.leaf (0))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (1))) (.branch 52 (.leaf (4)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (3))) (.branch 56 (.leaf (1)) (.leaf (5))))))))
  code := certificateP9_5592
  counts := ![(.branch 25 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 12 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-15))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 22 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 41 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (-3)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-50))),
  (.branch 26 (.leaf (0)) (.leaf (-31))),
  (.branch 45 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 50 (.branch 40 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4))))),
  (.branch 47 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))),
  (.branch 54 (.branch 41 (.leaf (-13)) (.leaf (-12))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-6)) (.leaf (-3))))),
  (.branch 49 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 56 (.leaf (-7)) (.leaf (-5)))),
  (.branch 54 (.branch 53 (.leaf (-10)) (.leaf (-8))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-4)) (.leaf (-2))))),
  (.branch 52 (.branch 39 (.leaf (-6)) (.branch 51 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.branch 53 (.leaf (-3)) (.leaf (-2))) (.branch 55 (.leaf (-1)) (.leaf (0))))),
  (.branch 32 (.branch 19 (.branch 13 (.branch 10 (.branch 8 (.leaf (-50)) (.branch 9 (.leaf (-49)) (.leaf (-48)))) (.branch 11 (.leaf (-47)) (.branch 12 (.leaf (-46)) (.leaf (-45))))) (.branch 16 (.branch 14 (.leaf (-44)) (.branch 15 (.leaf (-43)) (.leaf (-42)))) (.branch 17 (.leaf (-41)) (.branch 18 (.leaf (-40)) (.leaf (-39)))))) (.branch 25 (.branch 22 (.branch 20 (.leaf (-38)) (.branch 21 (.leaf (-37)) (.leaf (-36)))) (.branch 23 (.leaf (-35)) (.branch 24 (.leaf (-34)) (.leaf (-33))))) (.branch 28 (.branch 26 (.leaf (-32)) (.branch 27 (.leaf (-31)) (.leaf (-30)))) (.branch 30 (.branch 29 (.leaf (-29)) (.leaf (-28))) (.branch 31 (.leaf (-27)) (.leaf (-26))))))) (.branch 44 (.branch 38 (.branch 35 (.branch 33 (.leaf (-25)) (.branch 34 (.leaf (-24)) (.leaf (-23)))) (.branch 36 (.leaf (-22)) (.branch 37 (.leaf (-21)) (.leaf (-20))))) (.branch 41 (.branch 39 (.leaf (-19)) (.branch 40 (.leaf (-18)) (.leaf (-17)))) (.branch 42 (.leaf (-16)) (.branch 43 (.leaf (-15)) (.leaf (-14)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))) (.branch 48 (.leaf (-10)) (.branch 49 (.leaf (-9)) (.leaf (-8))))) (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 33 (.branch 29 (.branch 27 (.leaf (-31)) (.branch 28 (.leaf (-30)) (.leaf (-29)))) (.branch 31 (.branch 30 (.leaf (-28)) (.leaf (-27))) (.branch 32 (.leaf (-26)) (.leaf (-25))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-24)) (.leaf (-23))) (.branch 36 (.leaf (-22)) (.leaf (-21)))) (.branch 39 (.branch 38 (.leaf (-20)) (.leaf (-19))) (.branch 40 (.leaf (-18)) (.leaf (-17)))))) (.branch 49 (.branch 45 (.branch 43 (.branch 42 (.leaf (-16)) (.leaf (-15))) (.branch 44 (.leaf (-14)) (.leaf (-13)))) (.branch 47 (.branch 46 (.leaf (-12)) (.leaf (-11))) (.branch 48 (.leaf (-10)) (.leaf (-9))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-11)) (.leaf (-10)))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 54 (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_303_5593 : CycleWitness 9 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (7))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (1)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (4))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (8)) (.branch 23 (.leaf (1)) (.leaf (3)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (2)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (6)) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (4))) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (7)) (.branch 37 (.leaf (1)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (4)) (.leaf (1)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (5)) (.branch 44 (.leaf (0)) (.leaf (3)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (1))) (.branch 48 (.leaf (4)) (.leaf (0))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (8)) (.leaf (1))) (.branch 52 (.leaf (3)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (4))) (.branch 56 (.leaf (1)) (.leaf (6))))))))
  code := certificateP9_5593
  counts := ![(.branch 25 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 46 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 29 (.leaf (0)) (.branch 57 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-15))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-3)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-33))) (.branch 17 (.leaf (-34)) (.leaf (-35)))) (.branch 38 (.branch 31 (.leaf (-36)) (.leaf (-37))) (.branch 45 (.leaf (-38)) (.branch 52 (.leaf (-39)) (.leaf (-40)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-17)) (.leaf (-18)))) (.branch 26 (.leaf (-19)) (.branch 33 (.leaf (-20)) (.leaf (-21))))),
  (.branch 14 (.leaf (0)) (.leaf (-29))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-43))),
  (.branch 22 (.leaf (0)) (.branch 50 (.leaf (-13)) (.leaf (-14))))]
  high := ![(.branch 50 (.branch 40 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4))))),
  (.branch 52 (.leaf (-5)) (.leaf (-4))),
  (.branch 54 (.branch 47 (.leaf (-14)) (.leaf (-12))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-6)) (.leaf (-3))))),
  (.branch 54 (.branch 53 (.leaf (-40)) (.leaf (-32))) (.branch 55 (.leaf (-24)) (.branch 56 (.leaf (-16)) (.leaf (-8))))),
  (.branch 34 (.leaf (-21)) (.branch 56 (.leaf (-16)) (.leaf (-8)))),
  (.branch 49 (.branch 45 (.branch 15 (.leaf (-29)) (.branch 44 (.leaf (-28)) (.leaf (-26)))) (.branch 47 (.branch 46 (.leaf (-24)) (.leaf (-22))) (.branch 48 (.leaf (-20)) (.leaf (-18))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-16)) (.leaf (-14))) (.branch 52 (.leaf (-12)) (.leaf (-10)))) (.branch 55 (.branch 54 (.leaf (-8)) (.leaf (-6))) (.branch 56 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (0)),
  (.branch 46 (.branch 40 (.branch 37 (.branch 8 (.leaf (-43)) (.leaf (-42))) (.branch 38 (.leaf (-40)) (.branch 39 (.leaf (-38)) (.leaf (-36))))) (.branch 43 (.branch 41 (.leaf (-34)) (.branch 42 (.leaf (-32)) (.leaf (-30)))) (.branch 44 (.leaf (-28)) (.branch 45 (.leaf (-26)) (.leaf (-24)))))) (.branch 51 (.branch 48 (.branch 47 (.leaf (-22)) (.leaf (-20))) (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-16)) (.leaf (-14))))) (.branch 54 (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-10)) (.leaf (-8)))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-12)) (.leaf (-10)))) (.branch 55 (.branch 54 (.leaf (-8)) (.leaf (-6))) (.branch 56 (.leaf (-4)) (.leaf (-2)))))]
def witnessP9_303_5594 : CycleWitness 9 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (7))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (1))) (.branch 13 (.leaf (8)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (6)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (4))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (5)) (.branch 23 (.leaf (1)) (.leaf (7)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (2)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (4)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (8)) (.leaf (2))) (.branch 34 (.leaf (0)) (.leaf (5))))) (.branch 38 (.branch 36 (.leaf (6)) (.branch 37 (.leaf (1)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (4)) (.leaf (1)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (7)) (.branch 44 (.leaf (0)) (.leaf (5)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (3))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (1)) (.leaf (8))) (.branch 52 (.leaf (2)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (4)) (.leaf (6))) (.branch 56 (.leaf (1)) (.leaf (5))))))))
  code := certificateP9_5594
  counts := ![(.branch 25 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 12 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 46 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-15)) (.leaf (-17)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 31 (.leaf (-3)) (.branch 50 (.leaf (-4)) (.leaf (-5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 26 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 49 (.leaf (-10)) (.leaf (-11)))),
  (.branch 30 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 41 (.leaf (-6)) (.leaf (-7)))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (-1))) (.branch 45 (.leaf (-2)) (.leaf (-3)))),
  (.branch 17 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-14))),
  (.branch 13 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 54 (.branch 49 (.leaf (-17)) (.leaf (-16))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4))))),
  (.branch 51 (.leaf (-5)) (.leaf (-4))),
  (.branch 54 (.branch 53 (.leaf (-15)) (.leaf (-12))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-6)) (.leaf (-3))))),
  (.branch 53 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8)))) (.branch 55 (.branch 54 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.leaf (-4))))),
  (.branch 55 (.branch 42 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.leaf (-4)))),
  (.branch 47 (.branch 46 (.leaf (-3)) (.leaf (-2))) (.branch 48 (.leaf (-1)) (.leaf (0)))),
  (.branch 56 (.leaf (-2)) (.leaf (-1))),
  (.branch 50 (.branch 46 (.branch 44 (.leaf (-14)) (.branch 45 (.leaf (-13)) (.leaf (-12)))) (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.leaf (-8))))) (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_303_5595 : CycleWitness 9 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (7))) (.branch 13 (.leaf (2)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (8)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (6)) (.branch 23 (.leaf (2)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (7)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (3)) (.leaf (5)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.leaf (4))))) (.branch 38 (.branch 36 (.leaf (6)) (.branch 37 (.leaf (8)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (3))) (.branch 41 (.leaf (7)) (.leaf (2)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (4)))) (.branch 47 (.branch 46 (.leaf (5)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (3))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (6)) (.leaf (2))) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (4)) (.leaf (7))) (.branch 56 (.leaf (8)) (.leaf (1))))))))
  code := certificateP9_5595
  counts := ![(.branch 25 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 14 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 37 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-15)) (.leaf (-17)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-15)) (.leaf (-16)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-6)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (-45))) (.branch 31 (.leaf (-46)) (.leaf (-47)))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (-25))) (.branch 36 (.leaf (-26)) (.branch 50 (.leaf (-27)) (.leaf (-28))))),
  (.branch 12 (.leaf (0)) (.leaf (-9))),
  (.branch 18 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 54 (.branch 49 (.leaf (-17)) (.leaf (-16))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4))))),
  (.branch 48 (.leaf (-2)) (.branch 53 (.leaf (-1)) (.leaf (0)))),
  (.branch 54 (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-10)) (.leaf (-8)))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-4)) (.leaf (-2))))),
  (.branch 53 (.branch 51 (.branch 50 (.leaf (-16)) (.leaf (-14))) (.branch 52 (.leaf (-12)) (.leaf (-10)))) (.branch 55 (.branch 54 (.leaf (-8)) (.leaf (-6))) (.branch 56 (.leaf (-4)) (.leaf (-2))))),
  (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-4)) (.leaf (-2)))),
  (.branch 51 (.branch 48 (.branch 32 (.leaf (-47)) (.branch 47 (.leaf (-44)) (.leaf (-40)))) (.branch 49 (.leaf (-36)) (.branch 50 (.leaf (-32)) (.leaf (-28))))) (.branch 54 (.branch 52 (.leaf (-24)) (.branch 53 (.leaf (-20)) (.leaf (-16)))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 53 (.branch 51 (.leaf (-28)) (.branch 52 (.leaf (-24)) (.leaf (-20)))) (.branch 55 (.branch 54 (.leaf (-16)) (.leaf (-12))) (.branch 56 (.leaf (-8)) (.leaf (-4))))),
  (.branch 13 (.leaf (-9)) (.branch 56 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-1))]
def witnessP9_303_5596 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (5)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (7))) (.branch 27 (.leaf (0)) (.leaf (6)))))) (.branch 42 (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.leaf (3)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (0)) (.leaf (4))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (5)))) (.branch 53 (.branch 52 (.leaf (0)) (.leaf (8))) (.branch 55 (.leaf (0)) (.leaf (6)))))))
  code := certificateP9_5596
  counts := ![(.branch 27 (.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 8 (.leaf (5)) (.leaf (6))) (.branch 10 (.leaf (7)) (.branch 12 (.leaf (8)) (.leaf (9)))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (10)) (.leaf (11))) (.branch 17 (.leaf (12)) (.branch 19 (.leaf (13)) (.leaf (14))))) (.branch 23 (.branch 22 (.leaf (15)) (.leaf (16))) (.branch 24 (.leaf (17)) (.branch 26 (.leaf (18)) (.leaf (19))))))) (.branch 41 (.branch 34 (.branch 30 (.branch 29 (.leaf (20)) (.leaf (21))) (.branch 31 (.leaf (22)) (.branch 33 (.leaf (23)) (.leaf (24))))) (.branch 37 (.branch 36 (.leaf (25)) (.leaf (26))) (.branch 38 (.leaf (27)) (.branch 40 (.leaf (28)) (.leaf (29)))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (30)) (.leaf (31))) (.branch 45 (.leaf (32)) (.branch 47 (.leaf (33)) (.leaf (34))))) (.branch 52 (.branch 50 (.leaf (35)) (.branch 51 (.leaf (36)) (.leaf (37)))) (.branch 54 (.leaf (38)) (.branch 55 (.leaf (39)) (.leaf (40)))))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 56 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 53 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 3 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 14 (.leaf (0)) (.leaf (-14))),
  (.branch 21 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 25 (.leaf (0)) (.leaf (-31))),
  (.branch 53 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 53 (.leaf (-6)) (.leaf (-5))),
  (.branch 51 (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6))))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.branch 43 (.branch 41 (.branch 40 (.leaf (-17)) (.leaf (-16))) (.branch 42 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 40 (.branch 37 (.branch 36 (.leaf (-21)) (.leaf (-20))) (.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-18)) (.leaf (-17))))) (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_303_5597 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 8 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (6))))))) (.branch 42 (.branch 36 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (0))) (.branch 39 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (7)))))) (.branch 50 (.branch 46 (.branch 45 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (0)) (.branch 48 (.leaf (2)) (.leaf (0))))) (.branch 52 (.branch 51 (.leaf (4)) (.leaf (0))) (.branch 53 (.leaf (1)) (.branch 55 (.leaf (0)) (.leaf (8))))))))
  code := certificateP9_5597
  counts := ![(.branch 27 (.branch 13 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (9)) (.leaf (10))) (.branch 17 (.leaf (11)) (.leaf (12)))) (.branch 22 (.branch 21 (.leaf (13)) (.leaf (14))) (.branch 24 (.leaf (15)) (.branch 26 (.leaf (16)) (.leaf (17))))))) (.branch 41 (.branch 33 (.branch 30 (.branch 29 (.leaf (18)) (.leaf (19))) (.branch 31 (.leaf (20)) (.leaf (21)))) (.branch 36 (.branch 35 (.leaf (22)) (.leaf (23))) (.branch 38 (.leaf (24)) (.branch 40 (.leaf (25)) (.leaf (26)))))) (.branch 49 (.branch 44 (.branch 43 (.leaf (27)) (.leaf (28))) (.branch 45 (.leaf (29)) (.branch 47 (.leaf (30)) (.leaf (31))))) (.branch 52 (.branch 50 (.leaf (32)) (.leaf (33))) (.branch 54 (.leaf (34)) (.branch 55 (.leaf (35)) (.leaf (36)))))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 31 (.branch 17 (.leaf (-9)) (.leaf (-11))) (.branch 45 (.leaf (-13)) (.leaf (-15))))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-19))),
  (.branch 23 (.leaf (0)) (.leaf (-5))),
  (.branch 14 (.leaf (0)) (.leaf (-42))),
  (.branch 28 (.leaf (0)) (.leaf (-28))),
  (.branch 42 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 46 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 41 (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 43 (.branch 42 (.leaf (-15)) (.leaf (-14))) (.branch 44 (.leaf (-13)) (.branch 45 (.leaf (-12)) (.leaf (-11)))))) (.branch 51 (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6))))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 24 (.branch 19 (.branch 16 (.branch 15 (.leaf (-42)) (.leaf (-41))) (.branch 17 (.leaf (-40)) (.branch 18 (.leaf (-39)) (.leaf (-38))))) (.branch 21 (.branch 20 (.leaf (-37)) (.leaf (-36))) (.branch 22 (.leaf (-35)) (.branch 23 (.leaf (-34)) (.leaf (-33)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.branch 28 (.leaf (-29)) (.leaf (-28))))) (.branch 32 (.branch 30 (.leaf (-27)) (.branch 31 (.leaf (-26)) (.leaf (-25)))) (.branch 33 (.leaf (-24)) (.branch 34 (.leaf (-23)) (.leaf (-22))))))) (.branch 45 (.branch 40 (.branch 37 (.branch 36 (.leaf (-21)) (.leaf (-20))) (.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-18)) (.leaf (-17))))) (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (-28)) (.branch 30 (.leaf (-27)) (.leaf (-26)))) (.branch 33 (.branch 32 (.leaf (-25)) (.leaf (-24))) (.branch 34 (.leaf (-23)) (.leaf (-22))))) (.branch 38 (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19)))) (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_303_5598 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (8)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (4)) (.branch 27 (.leaf (0)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (6)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (3)) (.branch 41 (.leaf (0)) (.leaf (2)))))) (.branch 49 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (0)) (.branch 48 (.leaf (7)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (4)) (.branch 55 (.leaf (0)) (.leaf (2))))))))
  code := certificateP9_5598
  counts := ![(.branch 27 (.branch 13 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (9)) (.leaf (10))) (.branch 18 (.leaf (11)) (.leaf (12)))) (.branch 23 (.branch 21 (.leaf (13)) (.leaf (14))) (.branch 24 (.leaf (15)) (.branch 26 (.leaf (16)) (.leaf (17))))))) (.branch 41 (.branch 33 (.branch 30 (.branch 29 (.leaf (18)) (.leaf (19))) (.branch 32 (.leaf (20)) (.leaf (21)))) (.branch 37 (.branch 35 (.leaf (22)) (.leaf (23))) (.branch 38 (.leaf (24)) (.branch 40 (.leaf (25)) (.leaf (26)))))) (.branch 49 (.branch 44 (.branch 43 (.leaf (27)) (.leaf (28))) (.branch 46 (.leaf (29)) (.branch 47 (.leaf (30)) (.leaf (31))))) (.branch 52 (.branch 51 (.leaf (32)) (.leaf (33))) (.branch 54 (.leaf (34)) (.branch 55 (.leaf (35)) (.leaf (36)))))))),
  (.branch 22 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 53 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-8)))) (.branch 36 (.leaf (-10)) (.branch 50 (.leaf (-12)) (.leaf (-14))))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 25 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-50))),
  (.branch 34 (.leaf (0)) (.leaf (-22))),
  (.branch 48 (.leaf (0)) (.leaf (-8))),
  (.branch 20 (.leaf (0)) (.leaf (-36)))]
  high := ![(.branch 48 (.leaf (-11)) (.leaf (-9))),
  (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 54 (.leaf (-11)) (.branch 55 (.leaf (-10)) (.leaf (-9))))),
  (.leaf (0)),
  (.branch 47 (.branch 43 (.branch 41 (.branch 40 (.leaf (-17)) (.leaf (-16))) (.branch 42 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 18 (.branch 12 (.branch 9 (.branch 7 (.leaf (-50)) (.branch 8 (.leaf (-49)) (.leaf (-48)))) (.branch 10 (.leaf (-47)) (.branch 11 (.leaf (-46)) (.leaf (-45))))) (.branch 15 (.branch 13 (.leaf (-44)) (.branch 14 (.leaf (-43)) (.leaf (-42)))) (.branch 16 (.leaf (-41)) (.branch 17 (.leaf (-40)) (.leaf (-39)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-38)) (.branch 20 (.leaf (-37)) (.leaf (-36)))) (.branch 22 (.leaf (-35)) (.branch 23 (.leaf (-34)) (.leaf (-33))))) (.branch 27 (.branch 25 (.leaf (-32)) (.branch 26 (.leaf (-31)) (.leaf (-30)))) (.branch 29 (.branch 28 (.leaf (-29)) (.leaf (-28))) (.branch 30 (.leaf (-27)) (.leaf (-26))))))) (.branch 43 (.branch 37 (.branch 34 (.branch 32 (.leaf (-25)) (.branch 33 (.leaf (-24)) (.leaf (-23)))) (.branch 35 (.leaf (-22)) (.branch 36 (.leaf (-21)) (.leaf (-20))))) (.branch 40 (.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-18)) (.leaf (-17)))) (.branch 41 (.leaf (-16)) (.branch 42 (.leaf (-15)) (.leaf (-14)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (-13)) (.branch 45 (.leaf (-12)) (.leaf (-11)))) (.branch 47 (.leaf (-10)) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 45 (.branch 39 (.branch 36 (.branch 35 (.leaf (-22)) (.leaf (-21))) (.branch 37 (.leaf (-20)) (.branch 38 (.leaf (-19)) (.leaf (-18))))) (.branch 42 (.branch 40 (.leaf (-17)) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (-36)) (.leaf (-35))) (.branch 23 (.leaf (-34)) (.leaf (-33)))) (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.branch 28 (.leaf (-29)) (.leaf (-28)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-27)) (.leaf (-26))) (.branch 32 (.leaf (-25)) (.leaf (-24)))) (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))))) (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))))]
def witnessP9_303_5599 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (8)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (6)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (4)) (.leaf (1)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 47 (.leaf (1)) (.branch 48 (.leaf (2)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (1)) (.branch 51 (.leaf (0)) (.leaf (7)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (1))))))))
  code := certificateP9_5599
  counts := ![(.branch 26 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 15 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 23 (.leaf (10)) (.leaf (11)))))) (.branch 40 (.branch 32 (.branch 29 (.leaf (12)) (.branch 30 (.leaf (13)) (.leaf (14)))) (.branch 35 (.leaf (15)) (.branch 37 (.leaf (16)) (.leaf (17))))) (.branch 46 (.branch 43 (.leaf (18)) (.branch 44 (.leaf (19)) (.leaf (20)))) (.branch 51 (.branch 49 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24))))))),
  (.branch 28 (.branch 14 (.branch 5 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 42 (.branch 33 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 36 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 45 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 18 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 4 (.leaf (-6)) (.branch 16 (.leaf (-7)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-9)) (.leaf (-10))) (.branch 44 (.leaf (-11)) (.branch 46 (.leaf (-12)) (.leaf (-13)))))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 27 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-15))),
  (.branch 10 (.leaf (0)) (.leaf (-46))),
  (.branch 38 (.leaf (0)) (.leaf (-18))),
  (.branch 52 (.leaf (0)) (.leaf (-4))),
  (.branch 24 (.leaf (0)) (.leaf (-32)))]
  high := ![(.branch 52 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-10)))),
  (.branch 51 (.branch 48 (.leaf (-3)) (.leaf (-2))) (.branch 54 (.leaf (-1)) (.leaf (0)))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 48 (.branch 44 (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 21 (.branch 15 (.branch 12 (.branch 11 (.leaf (-46)) (.leaf (-45))) (.branch 13 (.leaf (-44)) (.branch 14 (.leaf (-43)) (.leaf (-42))))) (.branch 18 (.branch 16 (.leaf (-41)) (.branch 17 (.leaf (-40)) (.leaf (-39)))) (.branch 19 (.leaf (-38)) (.branch 20 (.leaf (-37)) (.leaf (-36)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-35)) (.branch 23 (.leaf (-34)) (.leaf (-33)))) (.branch 25 (.leaf (-32)) (.branch 26 (.leaf (-31)) (.leaf (-30))))) (.branch 30 (.branch 28 (.leaf (-29)) (.branch 29 (.leaf (-28)) (.leaf (-27)))) (.branch 31 (.leaf (-26)) (.branch 32 (.leaf (-25)) (.leaf (-24))))))) (.branch 44 (.branch 38 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))]
def witnessP9_303_5600 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 12 (.leaf (7)) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (0)))) (.branch 26 (.leaf (5)) (.branch 27 (.leaf (0)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (8)) (.branch 41 (.leaf (0)) (.leaf (1)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 47 (.leaf (4)) (.branch 48 (.leaf (0)) (.leaf (1))))) (.branch 53 (.branch 51 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 54 (.leaf (6)) (.branch 55 (.leaf (0)) (.leaf (1))))))))
  code := certificateP9_5600
  counts := ![(.branch 27 (.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 18 (.leaf (10)) (.leaf (11)))) (.branch 23 (.branch 22 (.leaf (12)) (.leaf (13))) (.branch 25 (.leaf (14)) (.leaf (15)))))) (.branch 41 (.branch 34 (.branch 30 (.branch 29 (.leaf (16)) (.leaf (17))) (.branch 32 (.leaf (18)) (.leaf (19)))) (.branch 37 (.branch 36 (.leaf (20)) (.leaf (21))) (.branch 39 (.leaf (22)) (.leaf (23))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (24)) (.leaf (25))) (.branch 46 (.leaf (26)) (.leaf (27)))) (.branch 51 (.branch 50 (.leaf (28)) (.leaf (29))) (.branch 53 (.leaf (30)) (.branch 55 (.leaf (31)) (.leaf (32)))))))),
  (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 5 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 19 (.leaf (0)) (.leaf (-37))),
  (.branch 47 (.leaf (0)) (.leaf (-9))),
  (.branch 26 (.leaf (0)) (.leaf (-30))),
  (.branch 54 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.leaf (0)) (.leaf (-44))),
  (.branch 40 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 52 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 44 (.branch 38 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (-37)) (.leaf (-36))) (.branch 22 (.leaf (-35)) (.leaf (-34)))) (.branch 25 (.branch 24 (.leaf (-33)) (.leaf (-32))) (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29)))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25)))) (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.branch 36 (.leaf (-21)) (.leaf (-20))))))) (.branch 46 (.branch 41 (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 43 (.branch 42 (.leaf (-15)) (.leaf (-14))) (.branch 44 (.leaf (-13)) (.branch 45 (.leaf (-12)) (.leaf (-11)))))) (.branch 51 (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6))))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.branch 33 (.branch 29 (.branch 27 (.leaf (-30)) (.branch 28 (.leaf (-29)) (.leaf (-28)))) (.branch 31 (.branch 30 (.leaf (-27)) (.leaf (-26))) (.branch 32 (.leaf (-25)) (.leaf (-24))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.leaf (-20)))) (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-17)) (.leaf (-16)))))) (.branch 48 (.branch 44 (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 23 (.branch 17 (.branch 14 (.branch 13 (.leaf (-44)) (.leaf (-43))) (.branch 15 (.leaf (-42)) (.branch 16 (.leaf (-41)) (.leaf (-40))))) (.branch 20 (.branch 18 (.leaf (-39)) (.branch 19 (.leaf (-38)) (.leaf (-37)))) (.branch 21 (.leaf (-36)) (.branch 22 (.leaf (-35)) (.leaf (-34)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-33)) (.leaf (-32))) (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29))))) (.branch 31 (.branch 29 (.leaf (-28)) (.branch 30 (.leaf (-27)) (.leaf (-26)))) (.branch 32 (.leaf (-25)) (.branch 33 (.leaf (-24)) (.leaf (-23))))))) (.branch 45 (.branch 39 (.branch 36 (.branch 35 (.leaf (-22)) (.leaf (-21))) (.branch 37 (.leaf (-20)) (.branch 38 (.leaf (-19)) (.leaf (-18))))) (.branch 42 (.branch 40 (.leaf (-17)) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_303_5601 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (7))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (5)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (3))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (6))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (4)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (0)) (.leaf (3)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 47 (.leaf (2)) (.branch 48 (.leaf (0)) (.leaf (8))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (5)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (3))))))))
  code := certificateP9_5601
  counts := ![(.branch 27 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 15 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))) (.branch 22 (.branch 20 (.leaf (10)) (.leaf (11))) (.branch 25 (.leaf (12)) (.leaf (13)))))) (.branch 41 (.branch 32 (.branch 29 (.leaf (14)) (.branch 30 (.leaf (15)) (.leaf (16)))) (.branch 36 (.branch 34 (.leaf (17)) (.leaf (18))) (.branch 39 (.leaf (19)) (.leaf (20))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 46 (.leaf (23)) (.leaf (24)))) (.branch 53 (.branch 50 (.leaf (25)) (.leaf (26))) (.branch 55 (.leaf (27)) (.leaf (28))))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-19))),
  (.branch 23 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 21 (.leaf (0)) (.leaf (-35))),
  (.branch 49 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 46 (.branch 41 (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 43 (.branch 42 (.leaf (-15)) (.leaf (-14))) (.branch 44 (.leaf (-13)) (.branch 45 (.leaf (-12)) (.leaf (-11)))))) (.branch 51 (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6))))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 40 (.branch 37 (.branch 36 (.leaf (-21)) (.leaf (-20))) (.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-18)) (.leaf (-17))))) (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 29 (.branch 25 (.branch 23 (.branch 22 (.leaf (-35)) (.leaf (-34))) (.branch 24 (.leaf (-33)) (.leaf (-32)))) (.branch 27 (.branch 26 (.leaf (-31)) (.leaf (-30))) (.branch 28 (.leaf (-29)) (.leaf (-28))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-27)) (.leaf (-26))) (.branch 32 (.leaf (-25)) (.leaf (-24)))) (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))))) (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_303_5602 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (7)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (3)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (4)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (5)) (.leaf (1)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (0)))) (.branch 47 (.leaf (1)) (.branch 48 (.leaf (8)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (2)) (.branch 51 (.leaf (0)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (6)) (.leaf (2))))))))
  code := certificateP9_5602
  counts := ![(.branch 26 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 15 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 23 (.leaf (10)) (.leaf (11)))))) (.branch 40 (.branch 32 (.branch 29 (.leaf (12)) (.branch 30 (.leaf (13)) (.leaf (14)))) (.branch 35 (.leaf (15)) (.branch 37 (.leaf (16)) (.leaf (17))))) (.branch 46 (.branch 43 (.leaf (18)) (.branch 44 (.leaf (19)) (.leaf (20)))) (.branch 51 (.branch 49 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24))))))),
  (.branch 25 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 33 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 18 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 4 (.leaf (-6)) (.branch 16 (.leaf (-7)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-9)) (.leaf (-10))) (.branch 44 (.leaf (-11)) (.branch 46 (.leaf (-12)) (.leaf (-13)))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 19 (.leaf (-16)) (.leaf (-17)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-22))),
  (.branch 13 (.leaf (0)) (.leaf (-15))),
  (.branch 27 (.leaf (0)) (.leaf (-1))),
  (.branch 20 (.leaf (0)) (.leaf (-36))),
  (.branch 48 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 52 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-10)))),
  (.branch 54 (.branch 48 (.leaf (-17)) (.leaf (-15))) (.branch 55 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (0)))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 39 (.branch 36 (.branch 35 (.leaf (-22)) (.leaf (-21))) (.branch 37 (.leaf (-20)) (.branch 38 (.leaf (-19)) (.leaf (-18))))) (.branch 42 (.branch 40 (.leaf (-17)) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 44 (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 38 (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (-36)) (.leaf (-35))) (.branch 23 (.leaf (-34)) (.leaf (-33)))) (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.branch 28 (.leaf (-29)) (.leaf (-28)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-27)) (.leaf (-26))) (.branch 32 (.leaf (-25)) (.leaf (-24)))) (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))))) (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_303_5603 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (6)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (4)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (7)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (6)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (5)) (.leaf (1)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (3)) (.leaf (0)))) (.branch 47 (.leaf (1)) (.branch 48 (.leaf (4)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (2)) (.branch 51 (.leaf (0)) (.leaf (8)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (5)) (.leaf (3))))))))
  code := certificateP9_5603
  counts := ![(.branch 26 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 15 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 23 (.leaf (10)) (.leaf (11)))))) (.branch 40 (.branch 32 (.branch 29 (.leaf (12)) (.branch 30 (.leaf (13)) (.leaf (14)))) (.branch 35 (.leaf (15)) (.branch 37 (.leaf (16)) (.leaf (17))))) (.branch 46 (.branch 43 (.leaf (18)) (.branch 44 (.leaf (19)) (.leaf (20)))) (.branch 51 (.branch 49 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24))))))),
  (.branch 25 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 18 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 4 (.leaf (-6)) (.branch 16 (.leaf (-7)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-9)) (.leaf (-10))) (.branch 44 (.leaf (-11)) (.branch 46 (.leaf (-12)) (.leaf (-13)))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 19 (.leaf (-16)) (.leaf (-17)))),
  (.branch 5 (.leaf (0)) (.leaf (-31))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (-1))) (.branch 33 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-18))),
  (.branch 24 (.leaf (0)) (.leaf (-32))),
  (.branch 52 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 52 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-10)))),
  (.branch 54 (.branch 48 (.leaf (-17)) (.leaf (-15))) (.branch 55 (.leaf (-10)) (.leaf (-5)))),
  (.branch 52 (.branch 6 (.leaf (-31)) (.branch 51 (.leaf (-30)) (.leaf (-25)))) (.branch 54 (.branch 53 (.leaf (-20)) (.leaf (-15))) (.branch 55 (.leaf (-10)) (.leaf (-5))))),
  (.branch 34 (.leaf (-3)) (.leaf (0))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_303_5604 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 15 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (4)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (7)) (.leaf (0)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (4)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (5))))))) (.branch 43 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 33 (.leaf (4)) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (0)))) (.branch 41 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 42 (.leaf (8)) (.leaf (0)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (0)) (.leaf (1)))) (.branch 47 (.leaf (0)) (.branch 48 (.leaf (4)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (3)) (.branch 51 (.leaf (0)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (6))))))))
  code := certificateP9_5604
  counts := ![(.branch 27 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 15 (.branch 13 (.leaf (7)) (.leaf (8))) (.branch 17 (.leaf (9)) (.leaf (10)))) (.branch 23 (.branch 21 (.leaf (11)) (.leaf (12))) (.branch 25 (.leaf (13)) (.leaf (14)))))) (.branch 41 (.branch 34 (.branch 30 (.branch 29 (.leaf (15)) (.leaf (16))) (.branch 32 (.leaf (17)) (.leaf (18)))) (.branch 38 (.branch 36 (.leaf (19)) (.leaf (20))) (.branch 40 (.leaf (21)) (.leaf (22))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (23)) (.leaf (24))) (.branch 47 (.leaf (25)) (.leaf (26)))) (.branch 53 (.branch 51 (.leaf (27)) (.leaf (28))) (.branch 55 (.leaf (29)) (.leaf (30))))))),
  (.branch 24 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 13 (.leaf (-14)) (.branch 41 (.leaf (-16)) (.leaf (-17))))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 28 (.leaf (0)) (.leaf (-28))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.leaf (-42))),
  (.branch 42 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 48 (.branch 44 (.branch 42 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 52 (.branch 50 (.leaf (-13)) (.leaf (-12))) (.branch 54 (.leaf (-11)) (.leaf (-10))))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.leaf (-8)) (.branch 55 (.leaf (-6)) (.leaf (-3)))),
  (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.branch 49 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (-28)) (.branch 30 (.leaf (-27)) (.leaf (-26)))) (.branch 33 (.branch 32 (.leaf (-25)) (.leaf (-24))) (.branch 34 (.leaf (-23)) (.leaf (-22))))) (.branch 38 (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19)))) (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0)),
  (.branch 35 (.branch 24 (.branch 19 (.branch 16 (.branch 15 (.leaf (-42)) (.leaf (-41))) (.branch 17 (.leaf (-40)) (.branch 18 (.leaf (-39)) (.leaf (-38))))) (.branch 21 (.branch 20 (.leaf (-37)) (.leaf (-36))) (.branch 22 (.leaf (-35)) (.branch 23 (.leaf (-34)) (.leaf (-33)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.branch 28 (.leaf (-29)) (.leaf (-28))))) (.branch 32 (.branch 30 (.leaf (-27)) (.branch 31 (.leaf (-26)) (.leaf (-25)))) (.branch 33 (.leaf (-24)) (.branch 34 (.leaf (-23)) (.leaf (-22))))))) (.branch 45 (.branch 40 (.branch 37 (.branch 36 (.leaf (-21)) (.leaf (-20))) (.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-18)) (.leaf (-17))))) (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_303_5605 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (4)) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (0)))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (0)) (.leaf (6)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 25 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (2)) (.leaf (0)))) (.branch 26 (.leaf (5)) (.branch 27 (.leaf (0)) (.leaf (7))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 33 (.leaf (4)) (.branch 34 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (0)) (.leaf (6)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 47 (.leaf (4)) (.branch 48 (.leaf (0)) (.leaf (3))))) (.branch 53 (.branch 51 (.leaf (0)) (.branch 52 (.leaf (2)) (.leaf (0)))) (.branch 54 (.leaf (5)) (.branch 55 (.leaf (0)) (.leaf (8))))))))
  code := certificateP9_5605
  counts := ![(.branch 27 (.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 18 (.leaf (10)) (.leaf (11)))) (.branch 23 (.branch 22 (.leaf (12)) (.leaf (13))) (.branch 25 (.leaf (14)) (.leaf (15)))))) (.branch 41 (.branch 34 (.branch 30 (.branch 29 (.leaf (16)) (.leaf (17))) (.branch 32 (.leaf (18)) (.leaf (19)))) (.branch 37 (.branch 36 (.leaf (20)) (.leaf (21))) (.branch 39 (.leaf (22)) (.leaf (23))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (24)) (.leaf (25))) (.branch 46 (.leaf (26)) (.leaf (27)))) (.branch 51 (.branch 50 (.leaf (28)) (.leaf (29))) (.branch 53 (.leaf (30)) (.branch 55 (.leaf (31)) (.leaf (32)))))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 14 (.leaf (0)) (.leaf (-14))),
  (.branch 28 (.leaf (0)) (.leaf (-28))),
  (.leaf (0))]
  high := ![(.branch 52 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))),
  (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (-28)) (.branch 30 (.leaf (-27)) (.leaf (-26)))) (.branch 33 (.branch 32 (.leaf (-25)) (.leaf (-24))) (.branch 34 (.leaf (-23)) (.leaf (-22))))) (.branch 38 (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19)))) (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessP9_303_5606 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 15 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (5)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (7)) (.leaf (0)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (6)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (4))))))) (.branch 43 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 33 (.leaf (5)) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (0)))) (.branch 41 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 42 (.leaf (8)) (.leaf (0)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (0)) (.leaf (1)))) (.branch 47 (.leaf (0)) (.branch 48 (.leaf (6)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (3)) (.branch 51 (.leaf (0)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (4))))))))
  code := certificateP9_5606
  counts := ![(.branch 27 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 15 (.branch 13 (.leaf (7)) (.leaf (8))) (.branch 17 (.leaf (9)) (.leaf (10)))) (.branch 23 (.branch 21 (.leaf (11)) (.leaf (12))) (.branch 25 (.leaf (13)) (.leaf (14)))))) (.branch 41 (.branch 34 (.branch 30 (.branch 29 (.leaf (15)) (.leaf (16))) (.branch 32 (.leaf (17)) (.leaf (18)))) (.branch 38 (.branch 36 (.leaf (19)) (.leaf (20))) (.branch 40 (.leaf (21)) (.leaf (22))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (23)) (.leaf (24))) (.branch 47 (.leaf (25)) (.leaf (26)))) (.branch 53 (.branch 51 (.leaf (27)) (.leaf (28))) (.branch 55 (.leaf (29)) (.leaf (30))))))),
  (.branch 24 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 54 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.leaf (0)) (.branch 56 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 13 (.leaf (-14)) (.branch 41 (.leaf (-16)) (.leaf (-17))))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 20 (.leaf (0)) (.leaf (-8))),
  (.branch 14 (.leaf (0)) (.leaf (-42))),
  (.branch 42 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 48 (.branch 44 (.branch 42 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 52 (.branch 50 (.leaf (-13)) (.leaf (-12))) (.branch 54 (.leaf (-11)) (.leaf (-10))))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.leaf (-8)) (.branch 55 (.leaf (-6)) (.leaf (-3)))),
  (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 44 (.branch 38 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 24 (.branch 19 (.branch 16 (.branch 15 (.leaf (-42)) (.leaf (-41))) (.branch 17 (.leaf (-40)) (.branch 18 (.leaf (-39)) (.leaf (-38))))) (.branch 21 (.branch 20 (.leaf (-37)) (.leaf (-36))) (.branch 22 (.leaf (-35)) (.branch 23 (.leaf (-34)) (.leaf (-33)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.branch 28 (.leaf (-29)) (.leaf (-28))))) (.branch 32 (.branch 30 (.leaf (-27)) (.branch 31 (.leaf (-26)) (.leaf (-25)))) (.branch 33 (.leaf (-24)) (.branch 34 (.leaf (-23)) (.leaf (-22))))))) (.branch 45 (.branch 40 (.branch 37 (.branch 36 (.leaf (-21)) (.leaf (-20))) (.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-18)) (.leaf (-17))))) (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_303_5607 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (3)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (2)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (7))) (.branch 27 (.leaf (2)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (2)) (.branch 37 (.leaf (0)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (6))) (.branch 41 (.leaf (2)) (.leaf (1)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (4)) (.branch 48 (.leaf (0)) (.leaf (1))))) (.branch 52 (.branch 50 (.leaf (2)) (.branch 51 (.leaf (0)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (8))) (.branch 55 (.leaf (2)) (.leaf (1))))))))
  code := certificateP9_5607
  counts := ![(.branch 25 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 39 (.branch 30 (.branch 29 (.leaf (10)) (.leaf (11))) (.branch 34 (.leaf (12)) (.branch 37 (.leaf (13)) (.leaf (14))))) (.branch 48 (.branch 43 (.leaf (15)) (.branch 44 (.leaf (16)) (.leaf (17)))) (.branch 51 (.leaf (18)) (.branch 53 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 5 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 16 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))) (.branch 30 (.leaf (-5)) (.branch 44 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-2)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 19 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-44))),
  (.branch 40 (.leaf (0)) (.leaf (-16))),
  (.branch 26 (.leaf (0)) (.leaf (-30))),
  (.branch 54 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 51 (.leaf (-4)) (.leaf (-3))),
  (.branch 44 (.branch 38 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 23 (.branch 17 (.branch 14 (.branch 13 (.leaf (-44)) (.leaf (-43))) (.branch 15 (.leaf (-42)) (.branch 16 (.leaf (-41)) (.leaf (-40))))) (.branch 20 (.branch 18 (.leaf (-39)) (.branch 19 (.leaf (-38)) (.leaf (-37)))) (.branch 21 (.leaf (-36)) (.branch 22 (.leaf (-35)) (.leaf (-34)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-33)) (.leaf (-32))) (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29))))) (.branch 31 (.branch 29 (.leaf (-28)) (.branch 30 (.leaf (-27)) (.leaf (-26)))) (.branch 32 (.leaf (-25)) (.branch 33 (.leaf (-24)) (.leaf (-23))))))) (.branch 45 (.branch 39 (.branch 36 (.branch 35 (.leaf (-22)) (.leaf (-21))) (.branch 37 (.leaf (-20)) (.branch 38 (.leaf (-19)) (.leaf (-18))))) (.branch 42 (.branch 40 (.leaf (-17)) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.branch 33 (.branch 29 (.branch 27 (.leaf (-30)) (.branch 28 (.leaf (-29)) (.leaf (-28)))) (.branch 31 (.branch 30 (.leaf (-27)) (.leaf (-26))) (.branch 32 (.leaf (-25)) (.leaf (-24))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.leaf (-20)))) (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-17)) (.leaf (-16)))))) (.branch 48 (.branch 44 (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 55 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_303_5608 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (3)) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (2)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (6)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (3))) (.branch 27 (.leaf (2)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (1)) (.branch 37 (.leaf (7)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (3))) (.branch 41 (.leaf (0)) (.leaf (1)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (4)) (.branch 44 (.leaf (2)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (3))) (.branch 48 (.leaf (0)) (.leaf (2))))) (.branch 52 (.branch 50 (.leaf (1)) (.branch 51 (.leaf (8)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (3))) (.branch 55 (.leaf (2)) (.leaf (1))))))))
  code := certificateP9_5608
  counts := ![(.branch 24 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 30 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.branch 52 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1))),
  (.branch 51 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 20 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 13 (.leaf (-6)) (.leaf (-7)))) (.branch 41 (.branch 30 (.leaf (-8)) (.leaf (-10))) (.branch 48 (.leaf (-11)) (.leaf (-12))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-3)) (.branch 45 (.leaf (-4)) (.leaf (-5))))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-10)) (.leaf (-11)))),
  (.branch 9 (.leaf (0)) (.leaf (-47))),
  (.branch 23 (.leaf (0)) (.leaf (-33))),
  (.branch 37 (.leaf (0)) (.leaf (-19))),
  (.branch 51 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9)))),
  (.branch 53 (.branch 51 (.leaf (-5)) (.branch 52 (.leaf (-4)) (.leaf (-3)))) (.branch 54 (.leaf (-2)) (.branch 55 (.leaf (-1)) (.leaf (0))))),
  (.branch 33 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 54 (.branch 44 (.leaf (-11)) (.leaf (-9))) (.branch 55 (.leaf (-6)) (.leaf (-3)))),
  (.branch 32 (.branch 20 (.branch 14 (.branch 11 (.branch 10 (.leaf (-47)) (.leaf (-46))) (.branch 12 (.leaf (-45)) (.branch 13 (.leaf (-44)) (.leaf (-43))))) (.branch 17 (.branch 15 (.leaf (-42)) (.branch 16 (.leaf (-41)) (.leaf (-40)))) (.branch 18 (.leaf (-39)) (.branch 19 (.leaf (-38)) (.leaf (-37)))))) (.branch 26 (.branch 23 (.branch 21 (.leaf (-36)) (.branch 22 (.leaf (-35)) (.leaf (-34)))) (.branch 24 (.leaf (-33)) (.branch 25 (.leaf (-32)) (.leaf (-31))))) (.branch 29 (.branch 27 (.leaf (-30)) (.branch 28 (.leaf (-29)) (.leaf (-28)))) (.branch 30 (.leaf (-27)) (.branch 31 (.leaf (-26)) (.leaf (-25))))))) (.branch 44 (.branch 38 (.branch 35 (.branch 33 (.leaf (-24)) (.branch 34 (.leaf (-23)) (.leaf (-22)))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 39 (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-33)) (.leaf (-32))) (.branch 26 (.leaf (-31)) (.leaf (-30)))) (.branch 29 (.branch 28 (.leaf (-29)) (.leaf (-28))) (.branch 30 (.leaf (-27)) (.leaf (-26))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-25)) (.leaf (-24))) (.branch 34 (.leaf (-23)) (.leaf (-22)))) (.branch 37 (.branch 36 (.leaf (-21)) (.leaf (-20))) (.branch 38 (.leaf (-19)) (.leaf (-18)))))) (.branch 47 (.branch 43 (.branch 41 (.branch 40 (.leaf (-17)) (.leaf (-16))) (.branch 42 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 46 (.branch 41 (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 43 (.branch 42 (.leaf (-15)) (.leaf (-14))) (.branch 44 (.leaf (-13)) (.branch 45 (.leaf (-12)) (.leaf (-11)))))) (.branch 51 (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6))))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))]
def witnessP9_303_5609 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (5)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (2)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 19 (.leaf (6)) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (7))) (.branch 27 (.leaf (3)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (5)) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (3)) (.branch 37 (.leaf (0)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (4))) (.branch 41 (.leaf (2)) (.leaf (1)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (3)))) (.branch 47 (.leaf (6)) (.branch 48 (.leaf (0)) (.leaf (1))))) (.branch 52 (.branch 50 (.leaf (2)) (.branch 51 (.leaf (0)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (8))) (.branch 55 (.leaf (3)) (.leaf (1))))))))
  code := certificateP9_5609
  counts := ![(.branch 25 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 39 (.branch 30 (.branch 29 (.leaf (10)) (.leaf (11))) (.branch 34 (.leaf (12)) (.branch 37 (.leaf (13)) (.leaf (14))))) (.branch 48 (.branch 43 (.leaf (15)) (.branch 44 (.leaf (16)) (.leaf (17)))) (.branch 51 (.leaf (18)) (.branch 53 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 16 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))) (.branch 30 (.leaf (-5)) (.branch 44 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-16))) (.branch 22 (.leaf (-17)) (.leaf (-18)))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 12 (.leaf (0)) (.leaf (-16))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 19 (.leaf (0)) (.leaf (-9))),
  (.branch 26 (.leaf (0)) (.leaf (-30))),
  (.branch 54 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 53 (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-15)) (.leaf (-12)))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3))))),
  (.branch 37 (.leaf (-4)) (.leaf (-3))),
  (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 44 (.branch 38 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.branch 33 (.branch 29 (.branch 27 (.leaf (-30)) (.branch 28 (.leaf (-29)) (.leaf (-28)))) (.branch 31 (.branch 30 (.leaf (-27)) (.leaf (-26))) (.branch 32 (.leaf (-25)) (.leaf (-24))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.leaf (-20)))) (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-17)) (.leaf (-16)))))) (.branch 48 (.branch 44 (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 55 (.leaf (-2)) (.leaf (-1)))]
def witnessP9_303_5610 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (1)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (3)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (7)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (3)))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (5)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (6))) (.branch 41 (.leaf (1)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (4)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (2))))) (.branch 52 (.branch 50 (.leaf (1)) (.branch 51 (.leaf (0)) (.leaf (8)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (5)) (.leaf (1))))))))
  code := certificateP9_5610
  counts := ![(.branch 26 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 39 (.branch 30 (.branch 29 (.leaf (10)) (.leaf (11))) (.branch 33 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14))))) (.branch 48 (.branch 42 (.leaf (15)) (.branch 45 (.leaf (16)) (.leaf (17)))) (.branch 51 (.leaf (18)) (.branch 54 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 13 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 50 (.branch 47 (.leaf (14)) (.leaf (15))) (.branch 53 (.leaf (16)) (.branch 56 (.leaf (17)) (.leaf (18))))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 30 (.leaf (-34)) (.leaf (-42)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.branch 43 (.leaf (-5)) (.leaf (-7))))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 44 (.leaf (-14)) (.leaf (-16)))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (-29)) (.leaf (-31)))),
  (.branch 18 (.leaf (0)) (.branch 55 (.leaf (-2)) (.leaf (-3)))),
  (.branch 12 (.leaf (0)) (.leaf (-16))),
  (.branch 24 (.leaf (0)) (.leaf (-32))),
  (.branch 52 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 43 (.branch 34 (.branch 31 (.leaf (-42)) (.leaf (-41))) (.branch 37 (.leaf (-40)) (.branch 40 (.leaf (-39)) (.leaf (-38))))) (.branch 49 (.branch 46 (.leaf (-37)) (.leaf (-36))) (.branch 52 (.leaf (-35)) (.branch 55 (.leaf (-34)) (.leaf (-25)))))),
  (.branch 44 (.leaf (-7)) (.branch 54 (.leaf (-3)) (.leaf (0)))),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 47 (.branch 45 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11))))) (.branch 53 (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8)))) (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))))),
  (.branch 50 (.branch 47 (.branch 28 (.leaf (-31)) (.leaf (-30))) (.branch 48 (.leaf (-27)) (.branch 49 (.leaf (-24)) (.leaf (-21))))) (.branch 53 (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-15)) (.leaf (-12)))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (-3)),
  (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_303_5611 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (1)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (4)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (6)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (4)))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (3))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (7))) (.branch 41 (.leaf (1)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (3))))) (.branch 52 (.branch 50 (.leaf (1)) (.branch 51 (.leaf (0)) (.leaf (8)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (1))))))))
  code := certificateP9_5611
  counts := ![(.branch 26 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 39 (.branch 30 (.branch 29 (.leaf (10)) (.leaf (11))) (.branch 33 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14))))) (.branch 48 (.branch 42 (.leaf (15)) (.branch 45 (.leaf (16)) (.leaf (17)))) (.branch 51 (.leaf (18)) (.branch 54 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 13 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 50 (.branch 47 (.leaf (14)) (.leaf (15))) (.branch 53 (.leaf (16)) (.branch 56 (.leaf (17)) (.leaf (18))))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 30 (.leaf (-34)) (.leaf (-42)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.branch 43 (.leaf (-5)) (.leaf (-7))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (-1))) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 44 (.leaf (-14)) (.leaf (-16)))),
  (.branch 12 (.leaf (0)) (.leaf (-44))),
  (.branch 24 (.leaf (0)) (.leaf (-32))),
  (.branch 40 (.leaf (0)) (.leaf (-16))),
  (.branch 52 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 43 (.branch 34 (.branch 31 (.leaf (-42)) (.leaf (-41))) (.branch 37 (.leaf (-40)) (.branch 40 (.leaf (-39)) (.leaf (-38))))) (.branch 49 (.branch 46 (.leaf (-37)) (.leaf (-36))) (.branch 52 (.leaf (-35)) (.branch 55 (.leaf (-34)) (.leaf (-25)))))),
  (.branch 44 (.leaf (-7)) (.branch 54 (.leaf (-3)) (.leaf (0)))),
  (.leaf (-3)),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 47 (.branch 45 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11))))) (.branch 53 (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8)))) (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))))),
  (.branch 34 (.branch 23 (.branch 17 (.branch 14 (.branch 13 (.leaf (-44)) (.leaf (-43))) (.branch 15 (.leaf (-42)) (.branch 16 (.leaf (-41)) (.leaf (-40))))) (.branch 20 (.branch 18 (.leaf (-39)) (.branch 19 (.leaf (-38)) (.leaf (-37)))) (.branch 21 (.leaf (-36)) (.branch 22 (.leaf (-35)) (.leaf (-34)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-33)) (.leaf (-32))) (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29))))) (.branch 31 (.branch 29 (.leaf (-28)) (.branch 30 (.leaf (-27)) (.leaf (-26)))) (.branch 32 (.leaf (-25)) (.branch 33 (.leaf (-24)) (.leaf (-23))))))) (.branch 45 (.branch 39 (.branch 36 (.branch 35 (.leaf (-22)) (.leaf (-21))) (.branch 37 (.leaf (-20)) (.branch 38 (.leaf (-19)) (.leaf (-18))))) (.branch 42 (.branch 40 (.leaf (-17)) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_303_5612 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (1)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (6)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (7)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (5)))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (3))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (4))) (.branch 41 (.leaf (1)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (6)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (3))))) (.branch 52 (.branch 50 (.leaf (1)) (.branch 51 (.leaf (0)) (.leaf (8)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (1))))))))
  code := certificateP9_5612
  counts := ![(.branch 26 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 39 (.branch 30 (.branch 29 (.leaf (10)) (.leaf (11))) (.branch 33 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14))))) (.branch 48 (.branch 42 (.leaf (15)) (.branch 45 (.leaf (16)) (.leaf (17)))) (.branch 51 (.leaf (18)) (.branch 54 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 13 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 50 (.branch 47 (.leaf (14)) (.leaf (15))) (.branch 53 (.leaf (16)) (.branch 56 (.leaf (17)) (.leaf (18))))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 30 (.leaf (-34)) (.leaf (-42)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.branch 43 (.leaf (-5)) (.leaf (-7))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (-1))) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-16))),
  (.branch 4 (.leaf (0)) (.leaf (-24))),
  (.branch 16 (.leaf (0)) (.leaf (-12))),
  (.branch 24 (.leaf (0)) (.leaf (-32))),
  (.branch 52 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 43 (.branch 34 (.branch 31 (.leaf (-42)) (.leaf (-41))) (.branch 37 (.leaf (-40)) (.branch 40 (.leaf (-39)) (.leaf (-38))))) (.branch 49 (.branch 46 (.leaf (-37)) (.leaf (-36))) (.branch 52 (.leaf (-35)) (.branch 55 (.leaf (-34)) (.leaf (-25)))))),
  (.branch 44 (.leaf (-7)) (.branch 54 (.leaf (-3)) (.leaf (0)))),
  (.leaf (-3)),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 44 (.branch 38 (.branch 35 (.branch 33 (.leaf (-24)) (.branch 34 (.leaf (-23)) (.leaf (-22)))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))]
def witnessP9_303_5613 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (6))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (7)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (0)))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (5))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (3)) (.leaf (0))) (.branch 41 (.leaf (4)) (.leaf (1)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (0)))) (.branch 47 (.leaf (1)) (.branch 48 (.leaf (0)) (.leaf (6))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (8)) (.leaf (1))))))))
  code := certificateP9_5613
  counts := ![(.branch 26 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 15 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))) (.branch 22 (.branch 20 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.leaf (13)))))) (.branch 40 (.branch 32 (.branch 29 (.leaf (14)) (.branch 30 (.leaf (15)) (.leaf (16)))) (.branch 36 (.branch 34 (.leaf (17)) (.leaf (18))) (.branch 38 (.leaf (19)) (.leaf (20))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 46 (.leaf (23)) (.leaf (24)))) (.branch 52 (.branch 50 (.leaf (25)) (.leaf (26))) (.branch 54 (.leaf (27)) (.leaf (28))))))),
  (.branch 28 (.branch 14 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 55 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 13 (.leaf (0)) (.leaf (-15))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 21 (.leaf (0)) (.leaf (-7))),
  (.branch 27 (.leaf (0)) (.leaf (-29))),
  (.branch 55 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 52 (.leaf (-1)) (.leaf (0))),
  (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 48 (.branch 44 (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 40 (.branch 37 (.branch 36 (.leaf (-21)) (.leaf (-20))) (.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-18)) (.leaf (-17))))) (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 41 (.branch 34 (.branch 30 (.branch 28 (.leaf (-29)) (.branch 29 (.leaf (-28)) (.leaf (-27)))) (.branch 32 (.branch 31 (.leaf (-26)) (.leaf (-25))) (.branch 33 (.leaf (-24)) (.leaf (-23))))) (.branch 37 (.branch 35 (.leaf (-22)) (.branch 36 (.leaf (-21)) (.leaf (-20)))) (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-17)) (.leaf (-16)))))) (.branch 48 (.branch 44 (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessP9_303_5614 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 5 (.leaf (7)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (0)))) (.branch 19 (.leaf (8)) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (6)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (0)))) (.branch 33 (.leaf (7)) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (4)) (.branch 37 (.leaf (0)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (0)) (.leaf (1)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (3)) (.leaf (0)))) (.branch 47 (.leaf (8)) (.branch 48 (.leaf (0)) (.leaf (1))))) (.branch 52 (.branch 50 (.leaf (2)) (.branch 51 (.leaf (0)) (.leaf (6)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (4))) (.branch 55 (.leaf (0)) (.leaf (1))))))))
  code := certificateP9_5614
  counts := ![(.branch 27 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 15 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))) (.branch 23 (.branch 20 (.leaf (10)) (.leaf (11))) (.branch 25 (.leaf (12)) (.leaf (13)))))) (.branch 41 (.branch 32 (.branch 29 (.leaf (14)) (.branch 30 (.leaf (15)) (.leaf (16)))) (.branch 37 (.branch 34 (.leaf (17)) (.leaf (18))) (.branch 39 (.leaf (19)) (.leaf (20))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 46 (.leaf (23)) (.leaf (24)))) (.branch 53 (.branch 51 (.leaf (25)) (.leaf (26))) (.branch 55 (.leaf (27)) (.leaf (28))))))),
  (.branch 28 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-19)) (.leaf (-20)))),
  (.branch 8 (.leaf (0)) (.branch 26 (.leaf (-32)) (.leaf (-34)))),
  (.branch 17 (.leaf (0)) (.branch 54 (.leaf (-5)) (.leaf (-6)))),
  (.branch 10 (.leaf (0)) (.leaf (-18))),
  (.branch 24 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 19 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 49 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 52 (.branch 41 (.leaf (-20)) (.branch 51 (.leaf (-18)) (.leaf (-15)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-9))) (.branch 55 (.leaf (-6)) (.leaf (-3))))),
  (.branch 50 (.branch 47 (.branch 27 (.leaf (-34)) (.branch 46 (.leaf (-33)) (.leaf (-30)))) (.branch 48 (.leaf (-27)) (.branch 49 (.leaf (-24)) (.leaf (-21))))) (.branch 53 (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-15)) (.leaf (-12)))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 55 (.leaf (-6)) (.leaf (-3))),
  (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 44 (.branch 38 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_303_5615 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (1)))) (.branch 5 (.leaf (5)) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (7))) (.branch 13 (.leaf (1)) (.leaf (2)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (1)))) (.branch 19 (.leaf (6)) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (4))) (.branch 27 (.leaf (1)) (.leaf (3))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (1)))) (.branch 33 (.leaf (5)) (.branch 34 (.leaf (3)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (2)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (3)) (.leaf (8))) (.branch 41 (.leaf (1)) (.leaf (2)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (3)) (.leaf (1)))) (.branch 47 (.leaf (6)) (.branch 48 (.leaf (2)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (3)) (.branch 51 (.leaf (1)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (4))) (.branch 55 (.leaf (1)) (.leaf (3))))))))
  code := certificateP9_5615
  counts := ![(.branch 24 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 30 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.branch 52 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 34 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 16 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 30 (.leaf (-8)) (.branch 44 (.leaf (-10)) (.leaf (-12))))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-16)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 26 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 19 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-44))),
  (.branch 40 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9)))),
  (.leaf (-3)),
  (.branch 54 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 55 (.leaf (-10)) (.leaf (-5)))),
  (.branch 51 (.leaf (-2)) (.leaf (0))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.branch 38 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 23 (.branch 17 (.branch 14 (.branch 13 (.leaf (-44)) (.leaf (-43))) (.branch 15 (.leaf (-42)) (.branch 16 (.leaf (-41)) (.leaf (-40))))) (.branch 20 (.branch 18 (.leaf (-39)) (.branch 19 (.leaf (-38)) (.leaf (-37)))) (.branch 21 (.leaf (-36)) (.branch 22 (.leaf (-35)) (.leaf (-34)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-33)) (.leaf (-32))) (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29))))) (.branch 31 (.branch 29 (.leaf (-28)) (.branch 30 (.leaf (-27)) (.leaf (-26)))) (.branch 32 (.leaf (-25)) (.branch 33 (.leaf (-24)) (.leaf (-23))))))) (.branch 45 (.branch 39 (.branch 36 (.branch 35 (.leaf (-22)) (.leaf (-21))) (.branch 37 (.leaf (-20)) (.branch 38 (.leaf (-19)) (.leaf (-18))))) (.branch 42 (.branch 40 (.leaf (-17)) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))]
def witnessP9_303_5616 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (2)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (7)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (3)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (6)) (.leaf (5))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (4)) (.leaf (8))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (5)))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (3)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (6)) (.branch 37 (.leaf (2)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (7)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (5)) (.branch 44 (.leaf (3)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (6)) (.leaf (4))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (3)) (.leaf (1))) (.branch 55 (.leaf (5)) (.leaf (8))))))))
  code := certificateP9_5616
  counts := ![(.branch 24 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 30 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 52 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 56 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 24 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 13 (.leaf (-6)) (.leaf (-7)))) (.branch 41 (.branch 30 (.leaf (-8)) (.leaf (-10))) (.branch 52 (.leaf (-11)) (.leaf (-12))))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-36)) (.leaf (-37)))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (-6))) (.branch 32 (.leaf (-7)) (.branch 43 (.leaf (-8)) (.leaf (-9))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (-7))) (.branch 48 (.leaf (-10)) (.leaf (-12)))),
  (.branch 14 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9)))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 35 (.leaf (-10)) (.leaf (-9))) (.branch 55 (.leaf (-6)) (.leaf (-3)))),
  (.branch 52 (.branch 50 (.branch 16 (.leaf (-37)) (.leaf (-35))) (.branch 51 (.leaf (-30)) (.leaf (-25)))) (.branch 54 (.branch 53 (.leaf (-20)) (.leaf (-15))) (.branch 55 (.leaf (-10)) (.leaf (-5))))),
  (.branch 44 (.leaf (-9)) (.leaf (-5))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9)))) (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5))))),
  (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessP9_303_5617 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (7)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (8))) (.branch 13 (.leaf (0)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (6)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (7)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (4))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (8)))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (6))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (7))) (.branch 41 (.leaf (0)) (.leaf (4)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (0)) (.leaf (5)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (2))) (.branch 48 (.leaf (1)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (8)) (.branch 51 (.leaf (0)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (6)) (.leaf (4))))))))
  code := certificateP9_5617
  counts := ![(.branch 26 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 13 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 23 (.leaf (9)) (.leaf (10)))))) (.branch 41 (.branch 33 (.branch 29 (.leaf (11)) (.branch 30 (.leaf (12)) (.leaf (13)))) (.branch 36 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))) (.branch 49 (.branch 44 (.leaf (17)) (.branch 46 (.leaf (18)) (.leaf (19)))) (.branch 51 (.leaf (20)) (.branch 54 (.leaf (21)) (.leaf (22))))))),
  (.branch 24 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 30 (.leaf (-16)) (.leaf (-19)))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-7)))) (.branch 39 (.leaf (-12)) (.branch 52 (.leaf (-15)) (.leaf (-20))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 47 (.leaf (-19)) (.leaf (-21)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (-5))) (.branch 53 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-12))),
  (.branch 17 (.leaf (0)) (.branch 35 (.leaf (-2)) (.leaf (-3)))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (-15))) (.branch 40 (.leaf (-16)) (.leaf (-17)))),
  (.branch 12 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 52 (.branch 31 (.leaf (-19)) (.leaf (-18))) (.branch 55 (.leaf (-16)) (.leaf (-11)))),
  (.branch 54 (.branch 53 (.leaf (-20)) (.leaf (-19))) (.branch 55 (.leaf (-18)) (.leaf (-17)))),
  (.branch 51 (.branch 49 (.branch 48 (.leaf (-21)) (.leaf (-19))) (.branch 50 (.leaf (-17)) (.leaf (-15)))) (.branch 53 (.branch 52 (.leaf (-13)) (.leaf (-11))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-7)) (.leaf (-5)))))),
  (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-7)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 50 (.branch 47 (.branch 46 (.leaf (-12)) (.leaf (-11))) (.branch 48 (.leaf (-10)) (.branch 49 (.leaf (-9)) (.leaf (-8))))) (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.leaf (-4)) (.branch 55 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 36 (.leaf (-3)) (.leaf (-2))),
  (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-17)) (.leaf (-16))) (.branch 43 (.leaf (-15)) (.leaf (-14)))) (.branch 46 (.branch 45 (.leaf (-13)) (.leaf (-12))) (.branch 47 (.leaf (-11)) (.leaf (-10))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 51 (.leaf (-7)) (.leaf (-6)))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.leaf (-4)) (.branch 55 (.leaf (-3)) (.leaf (-2)))))]
def witnessP9_303_5618 : CycleWitness 9 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (0)))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (4)) (.leaf (0))) (.branch 41 (.leaf (7)) (.leaf (1)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (3)) (.leaf (0)))) (.branch 47 (.leaf (1)) (.branch 48 (.leaf (0)) (.leaf (2))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (8)) (.leaf (1))))))))
  code := certificateP9_5618
  counts := ![(.branch 26 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 15 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))) (.branch 22 (.branch 20 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.leaf (13)))))) (.branch 40 (.branch 32 (.branch 29 (.leaf (14)) (.branch 30 (.leaf (15)) (.leaf (16)))) (.branch 36 (.branch 34 (.leaf (17)) (.leaf (18))) (.branch 38 (.leaf (19)) (.leaf (20))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 46 (.leaf (23)) (.leaf (24)))) (.branch 52 (.branch 50 (.leaf (25)) (.leaf (26))) (.branch 54 (.leaf (27)) (.leaf (28))))))),
  (.branch 28 (.branch 14 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1))),
  (.branch 55 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 13 (.leaf (0)) (.leaf (-43))),
  (.branch 27 (.leaf (0)) (.leaf (-29))),
  (.branch 41 (.leaf (0)) (.leaf (-15))),
  (.branch 55 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 52 (.leaf (-1)) (.leaf (0))),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.branch 23 (.branch 18 (.branch 15 (.branch 14 (.leaf (-43)) (.leaf (-42))) (.branch 16 (.leaf (-41)) (.branch 17 (.leaf (-40)) (.leaf (-39))))) (.branch 20 (.branch 19 (.leaf (-38)) (.leaf (-37))) (.branch 21 (.leaf (-36)) (.branch 22 (.leaf (-35)) (.leaf (-34)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-33)) (.leaf (-32))) (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29))))) (.branch 31 (.branch 29 (.leaf (-28)) (.branch 30 (.leaf (-27)) (.leaf (-26)))) (.branch 32 (.leaf (-25)) (.branch 33 (.leaf (-24)) (.leaf (-23))))))) (.branch 45 (.branch 39 (.branch 36 (.branch 35 (.leaf (-22)) (.leaf (-21))) (.branch 37 (.leaf (-20)) (.branch 38 (.leaf (-19)) (.leaf (-18))))) (.branch 42 (.branch 40 (.leaf (-17)) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 34 (.branch 30 (.branch 28 (.leaf (-29)) (.branch 29 (.leaf (-28)) (.leaf (-27)))) (.branch 32 (.branch 31 (.leaf (-26)) (.leaf (-25))) (.branch 33 (.leaf (-24)) (.leaf (-23))))) (.branch 37 (.branch 35 (.leaf (-22)) (.branch 36 (.leaf (-21)) (.leaf (-20)))) (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-17)) (.leaf (-16)))))) (.branch 48 (.branch 44 (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 44 (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessP9_303 : Fin 52 → CycleWitness 9 := ![witnessP9_303_5567, witnessP9_303_5568, witnessP9_303_5569, witnessP9_303_5570, witnessP9_303_5571, witnessP9_303_5572, witnessP9_303_5573, witnessP9_303_5574, witnessP9_303_5575, witnessP9_303_5576, witnessP9_303_5577, witnessP9_303_5578, witnessP9_303_5579, witnessP9_303_5580, witnessP9_303_5581, witnessP9_303_5582, witnessP9_303_5583, witnessP9_303_5584, witnessP9_303_5585, witnessP9_303_5586, witnessP9_303_5587, witnessP9_303_5588, witnessP9_303_5589, witnessP9_303_5590, witnessP9_303_5591, witnessP9_303_5592, witnessP9_303_5593, witnessP9_303_5594, witnessP9_303_5595, witnessP9_303_5596, witnessP9_303_5597, witnessP9_303_5598, witnessP9_303_5599, witnessP9_303_5600, witnessP9_303_5601, witnessP9_303_5602, witnessP9_303_5603, witnessP9_303_5604, witnessP9_303_5605, witnessP9_303_5606, witnessP9_303_5607, witnessP9_303_5608, witnessP9_303_5609, witnessP9_303_5610, witnessP9_303_5611, witnessP9_303_5612, witnessP9_303_5613, witnessP9_303_5614, witnessP9_303_5615, witnessP9_303_5616, witnessP9_303_5617, witnessP9_303_5618]
end RealPinwheel.FiveSixths


