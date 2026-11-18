-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_022
-- name    : RealPinwheel_FiveSixths_WitnessD7_022
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:36:31.757295+00:00
-- url     : https://prove2.me/theorems/5b968b02-5bf4-47e0-bfc9-d15d74436998
-- title:
--   Exact witness block D7_022
-- statement:
--   These exact witnesses represent words 227 through 241 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 227–241; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_022_226 : CycleWitness 7 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (5))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (1))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (4))) (.branch 43 (.leaf (0)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (3)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (1)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (6))) (.branch 59 (.leaf (0)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (3)) (.leaf (0))) (.branch 63 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_226
  counts := ![(.branch 30 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 24 (.leaf (9)) (.branch 27 (.leaf (10)) (.leaf (11)))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14)))) (.branch 40 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17))))) (.branch 53 (.branch 49 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20)))) (.branch 59 (.branch 56 (.leaf (21)) (.leaf (22))) (.branch 62 (.leaf (23)) (.leaf (24))))))),
  (.branch 32 (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))))) (.branch 48 (.branch 38 (.branch 34 (.leaf (10)) (.leaf (11))) (.branch 41 (.leaf (12)) (.branch 44 (.leaf (13)) (.leaf (14))))) (.branch 57 (.branch 50 (.leaf (15)) (.branch 54 (.leaf (16)) (.leaf (17)))) (.branch 60 (.leaf (18)) (.branch 64 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 58 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))) (.branch 37 (.branch 21 (.leaf (-13)) (.leaf (-15))) (.branch 53 (.leaf (-17)) (.leaf (-19))))),
  (.branch 18 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 34 (.leaf (-6)) (.branch 50 (.leaf (-7)) (.leaf (-8))))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-22))),
  (.branch 26 (.leaf (0)) (.leaf (-38))),
  (.branch 58 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 57 (.branch 54 (.leaf (-19)) (.leaf (-18))) (.branch 60 (.leaf (-17)) (.branch 63 (.leaf (-16)) (.leaf (-12))))),
  (.branch 61 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 62 (.leaf (-3)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 62 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 53 (.branch 47 (.branch 44 (.branch 43 (.leaf (-22)) (.leaf (-21))) (.branch 45 (.leaf (-20)) (.branch 46 (.leaf (-19)) (.leaf (-18))))) (.branch 50 (.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 35 (.branch 30 (.branch 28 (.branch 27 (.leaf (-38)) (.leaf (-37))) (.branch 29 (.leaf (-36)) (.leaf (-35)))) (.branch 32 (.branch 31 (.leaf (-34)) (.leaf (-33))) (.branch 33 (.leaf (-32)) (.branch 34 (.leaf (-31)) (.leaf (-30)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-29)) (.leaf (-28))) (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-25))))) (.branch 42 (.branch 41 (.leaf (-24)) (.leaf (-23))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))))) (.branch 54 (.branch 49 (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_022_227 : CycleWitness 7 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (2))) (.branch 31 (.leaf (0)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (1)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (4)) (.leaf (0))) (.branch 43 (.leaf (6)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (2))) (.branch 47 (.leaf (0)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (1)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (4)) (.leaf (0))) (.branch 59 (.leaf (3)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (2))) (.branch 63 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_227
  counts := ![(.branch 31 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 15 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 26 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))) (.branch 47 (.branch 37 (.branch 33 (.leaf (13)) (.branch 35 (.leaf (14)) (.leaf (15)))) (.branch 42 (.branch 40 (.leaf (16)) (.leaf (17))) (.branch 45 (.leaf (18)) (.leaf (19))))) (.branch 55 (.branch 50 (.leaf (20)) (.branch 52 (.leaf (21)) (.leaf (22)))) (.branch 60 (.branch 58 (.leaf (23)) (.leaf (24))) (.branch 63 (.leaf (25)) (.leaf (26))))))),
  (.branch 29 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 39 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 56 (.branch 51 (.leaf (11)) (.leaf (12))) (.branch 61 (.leaf (13)) (.leaf (14)))))),
  (.branch 30 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 43 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.branch 37 (.leaf (-5)) (.leaf (-6))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 51 (.leaf (-31)) (.leaf (-42)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 36 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.branch 32 (.branch 11 (.leaf (0)) (.leaf (-31))) (.branch 53 (.leaf (-32)) (.leaf (-33)))),
  (.branch 21 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 53 (.leaf (-6)) (.branch 61 (.leaf (-5)) (.leaf (-4)))),
  (.branch 57 (.branch 52 (.leaf (-42)) (.leaf (-41))) (.branch 62 (.leaf (-40)) (.branch 63 (.leaf (-34)) (.leaf (-28))))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 61 (.branch 37 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-33)) (.leaf (-30))) (.branch 56 (.leaf (-27)) (.branch 57 (.leaf (-24)) (.leaf (-21))))) (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 22 (.leaf (-1)) (.leaf (0)))]
def witnessD7_022_228 : CycleWitness 7 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (6))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (0)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (2)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (5)))) (.branch 54 (.branch 53 (.leaf (3)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (3)) (.leaf (6)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_228
  counts := ![(.branch 29 (.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 45 (.branch 35 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 41 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 47 (.leaf (15)) (.branch 51 (.leaf (16)) (.leaf (17)))) (.branch 57 (.leaf (18)) (.branch 61 (.leaf (19)) (.leaf (20))))))),
  (.branch 30 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 37 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 25 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 9 (.leaf (-8)) (.branch 15 (.leaf (-10)) (.leaf (-12))))) (.branch 41 (.branch 35 (.leaf (-13)) (.leaf (-14))) (.branch 47 (.leaf (-16)) (.branch 57 (.leaf (-18)) (.leaf (-19)))))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 17 (.leaf (-4)) (.branch 49 (.leaf (-5)) (.leaf (-6))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 27 (.leaf (-14)) (.branch 59 (.leaf (-19)) (.leaf (-23))))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (-15)) (.leaf (-18)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (-3))) (.branch 60 (.leaf (-6)) (.leaf (-9))))]
  high := ![(.branch 62 (.branch 58 (.leaf (-19)) (.leaf (-18))) (.branch 63 (.leaf (-16)) (.leaf (-14)))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 50 (.leaf (-6)) (.branch 57 (.leaf (-5)) (.leaf (-4)))),
  (.branch 61 (.branch 60 (.leaf (-23)) (.leaf (-20))) (.branch 62 (.leaf (-17)) (.branch 63 (.leaf (-14)) (.leaf (-11))))),
  (.leaf (0)),
  (.branch 57 (.branch 54 (.branch 29 (.leaf (-18)) (.branch 53 (.leaf (-17)) (.leaf (-16)))) (.branch 55 (.leaf (-15)) (.branch 56 (.leaf (-14)) (.leaf (-13))))) (.branch 60 (.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-11)) (.leaf (-10)))) (.branch 62 (.branch 61 (.leaf (-9)) (.leaf (-8))) (.branch 63 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 62 (.branch 61 (.leaf (-9)) (.leaf (-8))) (.branch 63 (.leaf (-7)) (.leaf (-6))))]
def witnessD7_022_229 : CycleWitness 7 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (1)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (3)) (.leaf (6))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (5))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (3)) (.leaf (0))) (.branch 43 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (4))) (.branch 47 (.leaf (1)) (.leaf (6)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (0)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (4))) (.branch 55 (.leaf (0)) (.leaf (5))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (3)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (4)) (.leaf (6))))))))
  code := certificateD7_229
  counts := ![(.branch 29 (.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 45 (.branch 35 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 51 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 61 (.leaf (19)) (.leaf (20))))))),
  (.branch 30 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 38 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 43 (.leaf (9)) (.leaf (10)))) (.branch 57 (.branch 52 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 28 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 36 (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 19 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-14)))) (.branch 35 (.leaf (-15)) (.branch 51 (.leaf (-16)) (.leaf (-17))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))) (.branch 38 (.leaf (-11)) (.branch 47 (.leaf (-12)) (.leaf (-13))))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (-26))) (.branch 31 (.leaf (-28)) (.leaf (-29)))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))) (.branch 54 (.branch 36 (.leaf (-3)) (.leaf (-4))) (.branch 63 (.leaf (-6)) (.leaf (-7))))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 62 (.branch 52 (.leaf (-17)) (.leaf (-16))) (.branch 63 (.leaf (-12)) (.leaf (-8)))),
  (.branch 53 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 58 (.leaf (-11)) (.branch 63 (.leaf (-10)) (.leaf (-7))))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 61 (.branch 32 (.leaf (-29)) (.branch 60 (.leaf (-27)) (.leaf (-22)))) (.branch 62 (.leaf (-17)) (.branch 63 (.leaf (-12)) (.leaf (-7))))),
  (.leaf (-7)),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_022_230 : CycleWitness 7 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (3))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (2)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (2))) (.branch 47 (.leaf (1)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (3))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (2))) (.branch 63 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_230
  counts := ![(.branch 29 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 45 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 61 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 15 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))))) (.branch 47 (.branch 37 (.branch 34 (.leaf (10)) (.leaf (11))) (.branch 41 (.leaf (12)) (.branch 44 (.leaf (13)) (.leaf (14))))) (.branch 57 (.branch 50 (.leaf (15)) (.branch 53 (.leaf (16)) (.leaf (17)))) (.branch 60 (.leaf (18)) (.branch 63 (.leaf (19)) (.leaf (20))))))),
  (.branch 30 (.branch 14 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 51 (.leaf (12)) (.leaf (13))) (.branch 59 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 32 (.leaf (0)) (.leaf (1))),
  (.branch 64 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 16 (.leaf (0)) (.leaf (-16))),
  (.branch 32 (.leaf (0)) (.leaf (-32))),
  (.leaf (0))]
  high := ![(.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 54 (.leaf (-7)) (.leaf (-5))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.leaf (-13)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-32)) (.leaf (-31))) (.branch 35 (.leaf (-30)) (.leaf (-29)))) (.branch 38 (.branch 37 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.leaf (-25))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-24)) (.leaf (-23))) (.branch 43 (.leaf (-22)) (.leaf (-21)))) (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-18)) (.leaf (-17)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.leaf (-13)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_022_231 : CycleWitness 7 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (3))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (2))) (.branch 43 (.leaf (0)) (.leaf (4)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (3))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (2))) (.branch 59 (.leaf (0)) (.leaf (6)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_231
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 15 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 38 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 51 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 63 (.leaf (15)) (.leaf (16))))))),
  (.branch 32 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 60 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-20))),
  (.branch 28 (.leaf (0)) (.leaf (-36))),
  (.branch 60 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 56 (.leaf (-13)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 54 (.branch 49 (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16))))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 37 (.branch 32 (.branch 30 (.branch 29 (.leaf (-36)) (.leaf (-35))) (.branch 31 (.leaf (-34)) (.leaf (-33)))) (.branch 34 (.branch 33 (.leaf (-32)) (.leaf (-31))) (.branch 35 (.leaf (-30)) (.branch 36 (.leaf (-29)) (.leaf (-28)))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-27)) (.leaf (-26))) (.branch 40 (.leaf (-25)) (.leaf (-24)))) (.branch 43 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))))) (.branch 55 (.branch 50 (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 52 (.branch 51 (.leaf (-14)) (.leaf (-13))) (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_022_232 : CycleWitness 7 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (3))) (.branch 39 (.leaf (0)) (.leaf (4))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (3))) (.branch 55 (.leaf (0)) (.leaf (6))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (2)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_232
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 16 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 8 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 35 (.leaf (-6)) (.branch 51 (.leaf (-7)) (.leaf (-8))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (-1))) (.branch 48 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.leaf (-24))),
  (.branch 24 (.leaf (0)) (.leaf (-40))),
  (.branch 56 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 56 (.leaf (-13)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6)))),
  (.branch 55 (.branch 49 (.leaf (-3)) (.leaf (-2))) (.branch 61 (.leaf (-1)) (.leaf (0)))),
  (.branch 52 (.branch 46 (.branch 43 (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22)))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))))) (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 34 (.branch 29 (.branch 26 (.branch 25 (.leaf (-40)) (.leaf (-39))) (.branch 27 (.leaf (-38)) (.branch 28 (.leaf (-37)) (.leaf (-36))))) (.branch 31 (.branch 30 (.leaf (-35)) (.leaf (-34))) (.branch 32 (.leaf (-33)) (.branch 33 (.leaf (-32)) (.leaf (-31)))))) (.branch 39 (.branch 36 (.branch 35 (.leaf (-30)) (.leaf (-29))) (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26))))) (.branch 41 (.branch 40 (.leaf (-25)) (.leaf (-24))) (.branch 42 (.leaf (-23)) (.branch 43 (.leaf (-22)) (.leaf (-21))))))) (.branch 54 (.branch 49 (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16))))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_022_233 : CycleWitness 7 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (6))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (3))) (.branch 39 (.leaf (0)) (.leaf (4))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (6)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (5))) (.branch 55 (.leaf (0)) (.leaf (4))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (2)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (2)) (.leaf (6))))))))
  code := certificateD7_233
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 35 (.leaf (-6)) (.branch 51 (.leaf (-7)) (.leaf (-8))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (-5))) (.branch 48 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.branch 32 (.leaf (-19)) (.leaf (-22)))),
  (.leaf (0))]
  high := ![(.branch 56 (.leaf (-13)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6)))),
  (.branch 61 (.branch 49 (.leaf (-7)) (.leaf (-6))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 55 (.branch 33 (.leaf (-22)) (.leaf (-21))) (.branch 56 (.leaf (-19)) (.branch 57 (.leaf (-17)) (.leaf (-15))))) (.branch 61 (.branch 59 (.leaf (-13)) (.branch 60 (.leaf (-11)) (.leaf (-9)))) (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-5)) (.leaf (-3)))))),
  (.leaf (0))]
def witnessD7_022_234 : CycleWitness 7 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (1)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (4))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (6))) (.branch 43 (.leaf (0)) (.leaf (2)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (1)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (4))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (3))) (.branch 59 (.leaf (0)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_234
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))) (.branch 47 (.branch 38 (.branch 34 (.leaf (10)) (.leaf (11))) (.branch 41 (.leaf (12)) (.branch 45 (.leaf (13)) (.leaf (14))))) (.branch 57 (.branch 50 (.leaf (15)) (.branch 54 (.leaf (16)) (.leaf (17)))) (.branch 61 (.leaf (18)) (.branch 63 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.leaf (-13)))),
  (.branch 31 (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 18 (.leaf (-5)) (.leaf (-6)))) (.branch 47 (.branch 34 (.leaf (-7)) (.leaf (-8))) (.branch 50 (.leaf (-9)) (.branch 63 (.leaf (-10)) (.leaf (-11)))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-17)) (.leaf (-18)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-34))),
  (.branch 21 (.leaf (0)) (.branch 42 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 56 (.leaf (-13)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (-11)),
  (.branch 61 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 55 (.branch 11 (.leaf (-34)) (.branch 54 (.leaf (-33)) (.leaf (-30)))) (.branch 56 (.leaf (-27)) (.branch 57 (.leaf (-24)) (.leaf (-21))))) (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 43 (.leaf (-2)) (.leaf (0)))]
def witnessD7_022_235 : CycleWitness 7 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (6))) (.branch 19 (.leaf (3)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (1))) (.branch 39 (.leaf (6)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (1)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (4)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (6)) (.leaf (1))) (.branch 63 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_235
  counts := ![(.branch 31 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 40 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 56 (.branch 49 (.leaf (15)) (.branch 53 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 63 (.leaf (19)) (.leaf (20))))))),
  (.branch 30 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 55 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 58 (.leaf (16)) (.branch 62 (.leaf (17)) (.leaf (18))))))),
  (.branch 28 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 33 (.leaf (-10)) (.branch 36 (.leaf (-11)) (.leaf (-12))))),
  (.branch 23 (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 16 (.leaf (-8)) (.leaf (-11)))) (.branch 48 (.branch 26 (.leaf (-13)) (.leaf (-16))) (.branch 55 (.leaf (-18)) (.branch 58 (.leaf (-20)) (.leaf (-23)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 15 (.leaf (-19)) (.leaf (-21)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.branch 37 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-43))),
  (.branch 18 (.leaf (0)) (.branch 39 (.leaf (-10)) (.leaf (-11))))]
  high := ![(.branch 50 (.leaf (-12)) (.branch 60 (.leaf (-11)) (.leaf (-8)))),
  (.branch 59 (.leaf (-23)) (.branch 63 (.leaf (-22)) (.leaf (-18)))),
  (.branch 61 (.branch 48 (.leaf (-21)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 60 (.branch 58 (.leaf (-8)) (.branch 59 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.branch 61 (.leaf (-5)) (.leaf (-4))) (.branch 63 (.leaf (-3)) (.leaf (-2))))),
  (.branch 38 (.leaf (-2)) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.branch 56 (.branch 52 (.branch 8 (.leaf (-43)) (.branch 51 (.leaf (-42)) (.leaf (-39)))) (.branch 54 (.branch 53 (.leaf (-36)) (.leaf (-33))) (.branch 55 (.leaf (-30)) (.leaf (-27))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-24)) (.leaf (-21))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 62 (.branch 40 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))]
def witnessD7_022_236 : CycleWitness 7 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (2)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (0))) (.branch 23 (.leaf (6)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (1))) (.branch 39 (.leaf (3)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (6)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (2))) (.branch 47 (.leaf (0)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (5)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (1)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (2))) (.branch 63 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_236
  counts := ![(.branch 29 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 47 (.branch 36 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.branch 43 (.leaf (12)) (.leaf (13))))) (.branch 54 (.branch 50 (.leaf (14)) (.leaf (15))) (.branch 58 (.leaf (16)) (.branch 61 (.leaf (17)) (.leaf (18))))))),
  (.branch 31 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-23))) (.branch 11 (.leaf (-28)) (.branch 18 (.leaf (-29)) (.leaf (-30))))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (-4))) (.branch 48 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.branch 32 (.leaf (-10)) (.leaf (-12)))),
  (.leaf (0))]
  high := ![(.branch 62 (.branch 51 (.leaf (-30)) (.leaf (-27))) (.branch 63 (.leaf (-18)) (.leaf (-9)))),
  (.branch 35 (.leaf (-14)) (.branch 60 (.leaf (-13)) (.leaf (-9)))),
  (.branch 52 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 49 (.leaf (-7)) (.leaf (-6))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.branch 56 (.branch 33 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 61 (.branch 60 (.leaf (-7)) (.leaf (-6))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3)))))),
  (.leaf (0))]
def witnessD7_022_237 : CycleWitness 7 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (5))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (3)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (5)) (.leaf (3))) (.branch 39 (.leaf (0)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (6)) (.leaf (2))) (.branch 43 (.leaf (0)) (.leaf (4)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (3)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (5)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (3))) (.branch 55 (.leaf (0)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (6)) (.leaf (4))) (.branch 59 (.leaf (0)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (3)) (.leaf (5))))))))
  code := certificateD7_237
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 21 (.leaf (-12)) (.branch 53 (.leaf (-17)) (.leaf (-21))))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.branch 37 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 56 (.leaf (-13)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 54 (.leaf (-21)) (.leaf (-20))) (.branch 62 (.leaf (-17)) (.branch 63 (.leaf (-14)) (.leaf (-11))))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 60 (.branch 45 (.leaf (-8)) (.branch 59 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.branch 61 (.leaf (-5)) (.leaf (-4))) (.branch 63 (.leaf (-3)) (.leaf (-2))))),
  (.branch 38 (.leaf (-2)) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_022_238 : CycleWitness 7 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (5))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (4))) (.branch 31 (.leaf (3)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (5)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (3))) (.branch 39 (.leaf (4)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (6)) (.leaf (0))) (.branch 43 (.leaf (2)) (.leaf (5)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (3)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (4)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (3))) (.branch 55 (.leaf (0)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (6)) (.leaf (4))) (.branch 59 (.leaf (2)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (5))) (.branch 63 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_238
  counts := ![(.branch 28 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 55 (.branch 51 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 16 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.leaf (7))))),
  (.branch 35 (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 53 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 62 (.leaf (6)) (.leaf (7))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 14 (.leaf (-29)) (.branch 23 (.leaf (-30)) (.leaf (-31))))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 36 (.leaf (-4)) (.branch 52 (.leaf (-6)) (.leaf (-8))))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-43)) (.leaf (-44)))) (.branch 30 (.leaf (-45)) (.branch 39 (.leaf (-46)) (.leaf (-47))))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 9 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 61 (.branch 56 (.leaf (-31)) (.leaf (-28))) (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 62 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 53 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 60 (.branch 40 (.leaf (-47)) (.branch 59 (.leaf (-42)) (.leaf (-35)))) (.branch 62 (.branch 61 (.leaf (-28)) (.leaf (-21))) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 8 (.leaf (-15)) (.branch 63 (.leaf (-14)) (.leaf (-7)))),
  (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_022_239 : CycleWitness 7 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (4))) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (6)) (.leaf (3))) (.branch 18 (.leaf (0)) (.leaf (2)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (0))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (2)) (.leaf (0))) (.branch 26 (.leaf (5)) (.leaf (1)))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (4))) (.branch 30 (.leaf (3)) (.leaf (2))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (3)) (.leaf (0))) (.branch 37 (.leaf (6)) (.leaf (2))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (3)) (.leaf (0)))) (.branch 44 (.branch 43 (.leaf (2)) (.leaf (4))) (.branch 45 (.leaf (0)) (.leaf (1)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (5)) (.leaf (3))) (.branch 49 (.leaf (0)) (.leaf (2)))) (.branch 52 (.branch 51 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (3)) (.leaf (0))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (2)) (.leaf (0))) (.branch 57 (.leaf (6)) (.leaf (1)))) (.branch 60 (.branch 59 (.leaf (0)) (.leaf (4))) (.branch 61 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_239
  counts := ![(.branch 28 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 14 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 25 (.leaf (9)) (.leaf (10)))))) (.branch 45 (.branch 36 (.branch 32 (.leaf (11)) (.branch 34 (.leaf (12)) (.leaf (13)))) (.branch 40 (.leaf (14)) (.branch 42 (.leaf (15)) (.leaf (16))))) (.branch 54 (.branch 49 (.leaf (17)) (.branch 51 (.leaf (18)) (.leaf (19)))) (.branch 56 (.leaf (20)) (.branch 59 (.leaf (21)) (.leaf (22))))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 33 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 38 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))) (.branch 36 (.branch 25 (.leaf (-4)) (.leaf (-5))) (.branch 56 (.leaf (-6)) (.leaf (-7))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-21)) (.leaf (-22)))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (-2))) (.branch 43 (.leaf (-4)) (.branch 55 (.leaf (-5)) (.leaf (-7))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-3)) (.leaf (-4)))) (.branch 41 (.branch 35 (.leaf (-6)) (.leaf (-7))) (.branch 53 (.leaf (-8)) (.leaf (-10))))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (-44)) (.leaf (-46)))),
  (.branch 16 (.leaf (0)) (.branch 57 (.leaf (-14)) (.leaf (-15))))]
  high := ![(.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))),
  (.branch 59 (.branch 40 (.leaf (-22)) (.leaf (-20))) (.branch 60 (.leaf (-15)) (.branch 61 (.leaf (-10)) (.leaf (-5))))),
  (.branch 57 (.branch 56 (.leaf (-7)) (.leaf (-5))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-1)) (.leaf (0))))),
  (.branch 54 (.leaf (-10)) (.leaf (-9))),
  (.branch 45 (.leaf (-5)) (.branch 61 (.leaf (-4)) (.leaf (-2)))),
  (.branch 54 (.branch 50 (.branch 48 (.branch 27 (.leaf (-46)) (.leaf (-45))) (.branch 49 (.leaf (-42)) (.leaf (-39)))) (.branch 52 (.branch 51 (.leaf (-36)) (.leaf (-33))) (.branch 53 (.leaf (-30)) (.leaf (-27))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (-24)) (.leaf (-21))) (.branch 57 (.leaf (-18)) (.leaf (-15)))) (.branch 60 (.branch 59 (.leaf (-12)) (.leaf (-9))) (.branch 61 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 59 (.branch 58 (.leaf (-15)) (.leaf (-12))) (.branch 60 (.leaf (-9)) (.branch 61 (.leaf (-6)) (.leaf (-3)))))]
def witnessD7_022_240 : CycleWitness 7 where
  length := 62
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (2)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (6)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (3)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (4)) (.leaf (5)))) (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (3)) (.leaf (2))))))) (.branch 46 (.branch 38 (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 36 (.branch 35 (.leaf (3)) (.leaf (1))) (.branch 37 (.leaf (0)) (.leaf (6))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (2)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (4)))) (.branch 44 (.branch 43 (.leaf (1)) (.leaf (0))) (.branch 45 (.leaf (3)) (.leaf (2)))))) (.branch 54 (.branch 50 (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (5)) (.leaf (0)))) (.branch 52 (.branch 51 (.leaf (3)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (2))))) (.branch 58 (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (4)) (.leaf (6)))) (.branch 60 (.branch 59 (.leaf (1)) (.leaf (0))) (.branch 61 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_240
  counts := ![(.branch 29 (.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 44 (.branch 34 (.branch 32 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 41 (.leaf (13)) (.leaf (14))))) (.branch 53 (.branch 47 (.leaf (15)) (.branch 50 (.leaf (16)) (.leaf (17)))) (.branch 56 (.leaf (18)) (.branch 60 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 36 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-15)) (.leaf (-23)))) (.branch 34 (.leaf (-24)) (.branch 37 (.leaf (-26)) (.leaf (-27))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 12 (.leaf (-3)) (.branch 43 (.leaf (-4)) (.leaf (-5))))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 35 (.leaf (-7)) (.branch 51 (.leaf (-10)) (.leaf (-12))))),
  (.branch 11 (.leaf (0)) (.branch 26 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (-14)) (.leaf (-15)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (-3))) (.branch 58 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 57 (.branch 38 (.leaf (-27)) (.leaf (-26))) (.branch 61 (.leaf (-20)) (.leaf (-13)))),
  (.branch 60 (.leaf (-5)) (.branch 61 (.leaf (-4)) (.leaf (-3)))),
  (.branch 47 (.leaf (-2)) (.branch 55 (.leaf (-1)) (.leaf (0)))),
  (.branch 52 (.leaf (-12)) (.leaf (-11))),
  (.branch 59 (.branch 58 (.leaf (-10)) (.leaf (-8))) (.branch 60 (.leaf (-6)) (.branch 61 (.leaf (-4)) (.leaf (-2))))),
  (.branch 55 (.branch 51 (.branch 28 (.leaf (-15)) (.branch 50 (.leaf (-14)) (.leaf (-13)))) (.branch 53 (.branch 52 (.leaf (-12)) (.leaf (-11))) (.branch 54 (.leaf (-10)) (.leaf (-9))))) (.branch 58 (.branch 56 (.leaf (-8)) (.branch 57 (.leaf (-7)) (.leaf (-6)))) (.branch 60 (.branch 59 (.leaf (-5)) (.leaf (-4))) (.branch 61 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 60 (.branch 59 (.leaf (-5)) (.leaf (-4))) (.branch 61 (.leaf (-3)) (.leaf (-2))))]
def witnessD7_022 : Fin 15 → CycleWitness 7 := ![witnessD7_022_226, witnessD7_022_227, witnessD7_022_228, witnessD7_022_229, witnessD7_022_230, witnessD7_022_231, witnessD7_022_232, witnessD7_022_233, witnessD7_022_234, witnessD7_022_235, witnessD7_022_236, witnessD7_022_237, witnessD7_022_238, witnessD7_022_239, witnessD7_022_240]
end RealPinwheel.FiveSixths


