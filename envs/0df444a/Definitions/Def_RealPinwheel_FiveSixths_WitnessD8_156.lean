-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_156
-- name    : RealPinwheel_FiveSixths_WitnessD8_156
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:11:15.034062+00:00
-- url     : https://prove2.me/theorems/7e7c2e29-3563-4f3d-bf77-9f4e9cc02e81
-- title:
--   Exact witness block D8_156
-- statement:
--   These exact witnesses represent words 1401 through 1416 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1401–1416; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_156_1400 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (6)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (7)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (5))) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (0))) (.branch 40 (.leaf (6)) (.leaf (3)))) (.branch 43 (.branch 42 (.leaf (4)) (.leaf (0))) (.branch 44 (.leaf (1)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (5)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (3)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (7)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (0))) (.branch 59 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_1400
  counts := ![(.branch 28 (.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 33 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 36 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 51 (.branch 46 (.leaf (15)) (.branch 48 (.leaf (16)) (.leaf (17)))) (.branch 54 (.leaf (18)) (.branch 58 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 12 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 23 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 55 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 50 (.branch 42 (.leaf (-8)) (.leaf (-7))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_156_1401 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (5))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (1)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (7)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (5)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (4))) (.branch 21 (.leaf (0)) (.leaf (6))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (7)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (6))) (.branch 36 (.leaf (2)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (4)) (.leaf (0))) (.branch 40 (.leaf (1)) (.leaf (5)))) (.branch 43 (.branch 42 (.leaf (3)) (.leaf (0))) (.branch 44 (.leaf (7)) (.leaf (0)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (6)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (4))) (.branch 51 (.leaf (0)) (.leaf (5))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (6))) (.branch 59 (.leaf (7)) (.leaf (4))))))))
  code := certificateD8_1401
  counts := ![(.branch 27 (.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 33 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 51 (.branch 45 (.leaf (15)) (.branch 49 (.leaf (16)) (.leaf (17)))) (.branch 55 (.leaf (18)) (.branch 57 (.leaf (19)) (.leaf (20))))))),
  (.branch 24 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 24 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 54 (.leaf (-20)) (.leaf (-22)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 42 (.leaf (-18)) (.leaf (-21)))),
  (.branch 8 (.leaf (0)) (.branch 38 (.leaf (-3)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 55 (.leaf (-22)) (.branch 56 (.leaf (-19)) (.leaf (-16)))) (.branch 58 (.leaf (-13)) (.branch 59 (.leaf (-10)) (.leaf (-7))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 56 (.branch 54 (.branch 43 (.leaf (-21)) (.leaf (-20))) (.branch 55 (.leaf (-18)) (.leaf (-16)))) (.branch 58 (.branch 57 (.leaf (-14)) (.leaf (-12))) (.branch 59 (.leaf (-10)) (.leaf (-8))))),
  (.branch 52 (.branch 39 (.leaf (-6)) (.branch 51 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.branch 53 (.leaf (-3)) (.leaf (-2))) (.branch 55 (.leaf (-1)) (.leaf (0))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1))]
def witnessD8_156_1402 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (5))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (0))) (.branch 21 (.leaf (7)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (0)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (0))) (.branch 36 (.leaf (2)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (3)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (7)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (5))) (.branch 44 (.leaf (0)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (0))) (.branch 51 (.leaf (6)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (5))) (.branch 59 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_1402
  counts := ![(.branch 29 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 20 (.branch 16 (.leaf (7)) (.branch 18 (.leaf (8)) (.leaf (9)))) (.branch 25 (.branch 22 (.leaf (10)) (.leaf (11))) (.branch 27 (.leaf (12)) (.leaf (13)))))) (.branch 44 (.branch 35 (.branch 31 (.leaf (14)) (.branch 33 (.leaf (15)) (.leaf (16)))) (.branch 40 (.branch 37 (.leaf (17)) (.leaf (18))) (.branch 42 (.leaf (19)) (.leaf (20))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (21)) (.leaf (22))) (.branch 50 (.leaf (23)) (.leaf (24)))) (.branch 57 (.branch 55 (.leaf (25)) (.leaf (26))) (.branch 59 (.leaf (27)) (.leaf (28))))))),
  (.branch 24 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 5 (.leaf (-9)) (.branch 7 (.leaf (-10)) (.leaf (-11))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.branch 30 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0))]
  high := ![(.branch 53 (.leaf (-11)) (.leaf (-7))),
  (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-10)) (.leaf (-8)))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 57 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 55 (.branch 52 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_156_1403 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (4)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (3))) (.branch 51 (.leaf (0)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (7))) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_1403
  counts := ![(.branch 28 (.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 23 (.leaf (9)) (.branch 26 (.leaf (10)) (.leaf (11)))))) (.branch 43 (.branch 36 (.branch 31 (.leaf (12)) (.branch 33 (.leaf (13)) (.leaf (14)))) (.branch 38 (.leaf (15)) (.branch 41 (.leaf (16)) (.leaf (17))))) (.branch 51 (.branch 46 (.leaf (18)) (.branch 48 (.leaf (19)) (.leaf (20)))) (.branch 56 (.branch 53 (.leaf (21)) (.leaf (22))) (.branch 58 (.leaf (23)) (.leaf (24))))))),
  (.branch 29 (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))) (.branch 45 (.branch 35 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.branch 42 (.leaf (12)) (.leaf (13))))) (.branch 52 (.branch 49 (.leaf (14)) (.leaf (15))) (.branch 55 (.leaf (16)) (.branch 59 (.leaf (17)) (.leaf (18))))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-46))),
  (.branch 34 (.leaf (0)) (.leaf (-26))),
  (.branch 54 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 59 (.leaf (-4)) (.leaf (-2))),
  (.branch 56 (.leaf (-5)) (.leaf (-3))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-46)) (.leaf (-45))) (.branch 17 (.leaf (-44)) (.branch 18 (.leaf (-43)) (.leaf (-42))))) (.branch 22 (.branch 20 (.leaf (-41)) (.branch 21 (.leaf (-40)) (.leaf (-39)))) (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36)))))) (.branch 31 (.branch 28 (.branch 26 (.leaf (-35)) (.branch 27 (.leaf (-34)) (.leaf (-33)))) (.branch 29 (.leaf (-32)) (.branch 30 (.leaf (-31)) (.leaf (-30))))) (.branch 34 (.branch 32 (.leaf (-29)) (.branch 33 (.leaf (-28)) (.leaf (-27)))) (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24))))))) (.branch 48 (.branch 42 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_156_1404 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (5))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (6)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (7)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (5)) (.leaf (3))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (2))) (.branch 36 (.leaf (0)) (.leaf (3))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (7))) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (0))) (.branch 44 (.leaf (4)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (5)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (3))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (6))) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (7)) (.leaf (3))))))))
  code := certificateD8_1404
  counts := ![(.branch 28 (.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 23 (.leaf (9)) (.branch 26 (.leaf (10)) (.leaf (11)))))) (.branch 43 (.branch 36 (.branch 31 (.leaf (12)) (.branch 33 (.leaf (13)) (.leaf (14)))) (.branch 38 (.leaf (15)) (.branch 41 (.leaf (16)) (.leaf (17))))) (.branch 51 (.branch 46 (.leaf (18)) (.branch 48 (.leaf (19)) (.leaf (20)))) (.branch 56 (.branch 53 (.leaf (21)) (.leaf (22))) (.branch 58 (.leaf (23)) (.leaf (24))))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 59 (.leaf (-4)) (.leaf (-2))),
  (.branch 57 (.branch 48 (.leaf (-11)) (.branch 56 (.leaf (-10)) (.leaf (-8)))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD8_156_1405 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (5))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (3)) (.leaf (1))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 40 (.leaf (6)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (4)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (4)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (3)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (7))))))))
  code := certificateD8_1405
  counts := ![(.branch 29 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))) (.branch 43 (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.branch 41 (.leaf (14)) (.leaf (15))))) (.branch 52 (.branch 46 (.leaf (16)) (.branch 49 (.leaf (17)) (.leaf (18)))) (.branch 55 (.leaf (19)) (.branch 58 (.leaf (20)) (.leaf (21))))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 14 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 60 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 31 (.leaf (-13)) (.branch 51 (.leaf (-17)) (.leaf (-21))))),
  (.branch 20 (.leaf (0)) (.leaf (-40))),
  (.branch 40 (.leaf (0)) (.leaf (-20))),
  (.leaf (0))]
  high := ![(.branch 50 (.branch 44 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17)))) (.branch 56 (.branch 53 (.leaf (-16)) (.leaf (-15))) (.branch 59 (.leaf (-14)) (.leaf (-7))))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-21)) (.leaf (-20))) (.branch 54 (.leaf (-19)) (.leaf (-18)))) (.branch 57 (.branch 56 (.leaf (-17)) (.leaf (-16))) (.branch 58 (.leaf (-15)) (.branch 59 (.leaf (-14)) (.leaf (-13)))))),
  (.branch 40 (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-40)) (.leaf (-39))) (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36))))) (.branch 27 (.branch 26 (.leaf (-35)) (.leaf (-34))) (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-27)) (.leaf (-26))))) (.branch 37 (.branch 36 (.leaf (-25)) (.leaf (-24))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))))) (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_156_1406 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 23 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (6)) (.leaf (0))) (.branch 22 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.leaf (3)) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (4))))))) (.branch 45 (.branch 38 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (0))) (.branch 37 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (3)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (2)) (.leaf (0))) (.branch 44 (.leaf (1)) (.leaf (4)))))) (.branch 53 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (7)) (.leaf (0))) (.branch 52 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.leaf (3)) (.branch 55 (.leaf (0)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_1406
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 23 (.leaf (9)) (.branch 25 (.leaf (10)) (.leaf (11)))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (12)) (.branch 33 (.leaf (13)) (.leaf (14)))) (.branch 38 (.leaf (15)) (.branch 40 (.leaf (16)) (.leaf (17))))) (.branch 50 (.branch 46 (.leaf (18)) (.branch 48 (.leaf (19)) (.leaf (20)))) (.branch 55 (.branch 53 (.leaf (21)) (.leaf (22))) (.branch 58 (.leaf (23)) (.leaf (24))))))),
  (.branch 29 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 44 (.branch 36 (.branch 32 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 41 (.leaf (13)) (.leaf (14))))) (.branch 52 (.branch 47 (.leaf (15)) (.branch 51 (.leaf (16)) (.leaf (17)))) (.branch 56 (.leaf (18)) (.branch 59 (.leaf (19)) (.leaf (20))))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 22 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-5)) (.leaf (-11)))) (.branch 37 (.leaf (-16)) (.branch 52 (.leaf (-21)) (.leaf (-26))))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-26))),
  (.branch 19 (.leaf (0)) (.leaf (-41))),
  (.branch 49 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 56 (.leaf (-5)) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 53 (.leaf (-26)) (.leaf (-24))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (-41)) (.leaf (-40))) (.branch 22 (.leaf (-39)) (.branch 23 (.leaf (-38)) (.leaf (-37))))) (.branch 26 (.branch 25 (.leaf (-36)) (.leaf (-35))) (.branch 27 (.leaf (-34)) (.branch 28 (.leaf (-33)) (.leaf (-32)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-31)) (.leaf (-30))) (.branch 32 (.leaf (-29)) (.branch 33 (.leaf (-28)) (.leaf (-27))))) (.branch 36 (.branch 35 (.leaf (-26)) (.leaf (-25))) (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-23)) (.leaf (-22))))))) (.branch 49 (.branch 44 (.branch 41 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17))))) (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_156_1407 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (4))) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (4))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (4)) (.leaf (0))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (2)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (3))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (0))) (.branch 40 (.leaf (4)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (2))) (.branch 44 (.leaf (0)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (3)) (.branch 47 (.leaf (0)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (4)) (.leaf (0))) (.branch 51 (.leaf (1)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (7))) (.branch 55 (.leaf (1)) (.leaf (0)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_1407
  counts := ![(.branch 30 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))) (.branch 44 (.branch 36 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 39 (.leaf (13)) (.branch 41 (.leaf (14)) (.leaf (15))))) (.branch 53 (.branch 47 (.leaf (16)) (.branch 50 (.leaf (17)) (.leaf (18)))) (.branch 56 (.leaf (19)) (.branch 59 (.leaf (20)) (.leaf (21))))))),
  (.branch 28 (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))) (.branch 45 (.branch 35 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.branch 42 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 48 (.leaf (14)) (.leaf (15))) (.branch 55 (.leaf (16)) (.branch 58 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 8 (.leaf (-5)) (.branch 11 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-46))),
  (.branch 34 (.leaf (0)) (.leaf (-26))),
  (.branch 54 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 48 (.branch 42 (.leaf (-13)) (.branch 45 (.leaf (-12)) (.leaf (-11)))) (.branch 54 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.leaf (-7))))),
  (.branch 52 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 58 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 50 (.leaf (-1)) (.leaf (0))),
  (.branch 37 (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-46)) (.leaf (-45))) (.branch 17 (.leaf (-44)) (.branch 18 (.leaf (-43)) (.leaf (-42))))) (.branch 22 (.branch 20 (.leaf (-41)) (.branch 21 (.leaf (-40)) (.leaf (-39)))) (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36)))))) (.branch 31 (.branch 28 (.branch 26 (.leaf (-35)) (.branch 27 (.leaf (-34)) (.leaf (-33)))) (.branch 29 (.leaf (-32)) (.branch 30 (.leaf (-31)) (.leaf (-30))))) (.branch 34 (.branch 32 (.leaf (-29)) (.branch 33 (.leaf (-28)) (.leaf (-27)))) (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24))))))) (.branch 48 (.branch 42 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))) (.branch 45 (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))))) (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_156_1408 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (4))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (7))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (1))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (5))) (.branch 40 (.leaf (0)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (3)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (6))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (3)) (.leaf (1))))))))
  code := certificateD8_1408
  counts := ![(.branch 28 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 40 (.leaf (13)) (.leaf (14))))) (.branch 52 (.branch 46 (.leaf (15)) (.branch 49 (.leaf (16)) (.leaf (17)))) (.branch 55 (.leaf (18)) (.branch 58 (.leaf (19)) (.leaf (20))))))),
  (.branch 30 (.branch 15 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 45 (.branch 35 (.branch 32 (.leaf (10)) (.leaf (11))) (.branch 38 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 53 (.branch 47 (.leaf (15)) (.branch 50 (.leaf (16)) (.leaf (17)))) (.branch 57 (.leaf (18)) (.branch 60 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-51))),
  (.branch 39 (.leaf (0)) (.leaf (-21))),
  (.branch 54 (.leaf (0)) (.leaf (-6))),
  (.branch 24 (.leaf (0)) (.leaf (-36)))]
  high := ![(.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 54 (.leaf (-1)) (.leaf (0))),
  (.branch 57 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 52 (.leaf (-3)) (.leaf (-2))),
  (.branch 34 (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-51)) (.branch 11 (.leaf (-50)) (.leaf (-49)))) (.branch 13 (.leaf (-48)) (.branch 14 (.leaf (-47)) (.leaf (-46))))) (.branch 18 (.branch 16 (.leaf (-45)) (.branch 17 (.leaf (-44)) (.leaf (-43)))) (.branch 19 (.leaf (-42)) (.branch 20 (.leaf (-41)) (.leaf (-40)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-39)) (.branch 23 (.leaf (-38)) (.leaf (-37)))) (.branch 25 (.leaf (-36)) (.branch 26 (.leaf (-35)) (.leaf (-34))))) (.branch 30 (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))) (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.leaf (-27))))))) (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 44 (.branch 41 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17))))) (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-36)) (.leaf (-35))) (.branch 27 (.leaf (-34)) (.leaf (-33)))) (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))))) (.branch 51 (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))))]
def witnessD8_156_1409 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (4)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (1)) (.leaf (5)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_1409
  counts := ![(.branch 28 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 40 (.leaf (13)) (.leaf (14))))) (.branch 52 (.branch 46 (.leaf (15)) (.branch 49 (.leaf (16)) (.leaf (17)))) (.branch 55 (.leaf (18)) (.branch 58 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 14 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 44 (.branch 35 (.branch 32 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 54 (.branch 47 (.leaf (15)) (.branch 50 (.leaf (16)) (.leaf (17)))) (.branch 57 (.leaf (18)) (.branch 59 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 60 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.branch 30 (.leaf (0)) (.leaf (-30))),
  (.leaf (0))]
  high := ![(.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 57 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28)))) (.branch 35 (.branch 34 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-25)) (.leaf (-24))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.leaf (-20)))) (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_156_1410 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (4)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (3)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (5)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (3)) (.leaf (2))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (2))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (6)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (3)) (.leaf (2)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (2))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (7)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (3)) (.leaf (2))))))))
  code := certificateD8_1410
  counts := ![(.branch 27 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 34 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 29 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 55 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-50))),
  (.branch 25 (.leaf (0)) (.leaf (-35))),
  (.branch 40 (.leaf (0)) (.leaf (-20))),
  (.branch 55 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 54 (.branch 50 (.leaf (-14)) (.leaf (-13))) (.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-8)) (.leaf (-4))))),
  (.branch 55 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 59 (.leaf (-8)) (.leaf (-4)))),
  (.branch 53 (.branch 49 (.leaf (-3)) (.leaf (-2))) (.branch 57 (.leaf (-1)) (.leaf (0)))),
  (.branch 52 (.leaf (-3)) (.leaf (-2))),
  (.branch 35 (.branch 22 (.branch 16 (.branch 13 (.branch 11 (.leaf (-50)) (.branch 12 (.leaf (-49)) (.leaf (-48)))) (.branch 14 (.leaf (-47)) (.branch 15 (.leaf (-46)) (.leaf (-45))))) (.branch 19 (.branch 17 (.leaf (-44)) (.branch 18 (.leaf (-43)) (.leaf (-42)))) (.branch 20 (.leaf (-41)) (.branch 21 (.leaf (-40)) (.leaf (-39)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-38)) (.branch 24 (.leaf (-37)) (.leaf (-36)))) (.branch 26 (.leaf (-35)) (.branch 27 (.leaf (-34)) (.leaf (-33))))) (.branch 31 (.branch 29 (.leaf (-32)) (.branch 30 (.leaf (-31)) (.leaf (-30)))) (.branch 33 (.branch 32 (.leaf (-29)) (.leaf (-28))) (.branch 34 (.leaf (-27)) (.leaf (-26))))))) (.branch 47 (.branch 41 (.branch 38 (.branch 36 (.leaf (-25)) (.branch 37 (.leaf (-24)) (.leaf (-23)))) (.branch 39 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20))))) (.branch 44 (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17)))) (.branch 45 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-35)) (.leaf (-34))) (.branch 28 (.leaf (-33)) (.leaf (-32)))) (.branch 31 (.branch 30 (.leaf (-31)) (.leaf (-30))) (.branch 32 (.leaf (-29)) (.leaf (-28))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))))) (.branch 51 (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 50 (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))))) (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_156_1411 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (6)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (7))) (.branch 21 (.leaf (0)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (5)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (0)) (.leaf (4))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (1)) (.leaf (0))) (.branch 40 (.leaf (7)) (.leaf (2)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (5)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (6))) (.branch 51 (.leaf (0)) (.leaf (4))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (2)))) (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (5)) (.leaf (7))))))))
  code := certificateD8_1411
  counts := ![(.branch 28 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 36 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 51 (.branch 46 (.leaf (15)) (.branch 49 (.leaf (16)) (.leaf (17)))) (.branch 54 (.leaf (18)) (.branch 58 (.leaf (19)) (.leaf (20))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 55 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_156_1412 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (1)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (6))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (1)) (.leaf (4)))) (.branch 43 (.branch 42 (.leaf (0)) (.leaf (2))) (.branch 44 (.leaf (1)) (.leaf (5)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (4)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_1412
  counts := ![(.branch 27 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 42 (.branch 34 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 52 (.branch 46 (.leaf (15)) (.branch 49 (.leaf (16)) (.leaf (17)))) (.branch 54 (.leaf (18)) (.branch 57 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 55 (.leaf (14)) (.branch 59 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 60 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.branch 30 (.leaf (0)) (.leaf (-30))),
  (.leaf (0))]
  high := ![(.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.branch 48 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.leaf (-4)))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 55 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6))))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28)))) (.branch 35 (.branch 34 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-25)) (.leaf (-24))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.leaf (-20)))) (.branch 43 (.branch 42 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-16)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_156_1413 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (4))) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (5))) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (1))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (6))) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 43 (.branch 42 (.leaf (3)) (.leaf (0))) (.branch 44 (.leaf (2)) (.leaf (1)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (1)) (.leaf (0))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (2)) (.leaf (7))) (.branch 55 (.leaf (0)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (3)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (1))))))))
  code := certificateD8_1413
  counts := ![(.branch 28 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 37 (.leaf (12)) (.branch 40 (.leaf (13)) (.leaf (14))))) (.branch 52 (.branch 46 (.leaf (15)) (.branch 49 (.leaf (16)) (.leaf (17)))) (.branch 55 (.leaf (18)) (.branch 58 (.leaf (19)) (.leaf (20))))))),
  (.branch 30 (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 36 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.branch 60 (.leaf (15)) (.leaf (16))))))),
  (.branch 29 (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 17 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 32 (.leaf (-3)) (.branch 47 (.leaf (-4)) (.leaf (-5))))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-51))),
  (.branch 24 (.leaf (0)) (.leaf (-36))),
  (.branch 39 (.leaf (0)) (.leaf (-21))),
  (.branch 54 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.leaf (-2)) (.leaf (-1))),
  (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 34 (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-51)) (.branch 11 (.leaf (-50)) (.leaf (-49)))) (.branch 13 (.leaf (-48)) (.branch 14 (.leaf (-47)) (.leaf (-46))))) (.branch 18 (.branch 16 (.leaf (-45)) (.branch 17 (.leaf (-44)) (.leaf (-43)))) (.branch 19 (.leaf (-42)) (.branch 20 (.leaf (-41)) (.leaf (-40)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-39)) (.branch 23 (.leaf (-38)) (.leaf (-37)))) (.branch 25 (.leaf (-36)) (.branch 26 (.leaf (-35)) (.leaf (-34))))) (.branch 30 (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))) (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.leaf (-27))))))) (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-36)) (.leaf (-35))) (.branch 27 (.leaf (-34)) (.leaf (-33)))) (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-28)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 39 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-20)) (.leaf (-19))))))) (.branch 51 (.branch 46 (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))))) (.branch 55 (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 57 (.branch 56 (.leaf (-5)) (.leaf (-4))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 44 (.branch 41 (.branch 40 (.leaf (-21)) (.leaf (-20))) (.branch 42 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-17))))) (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))))) (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_156_1414 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (6))) (.branch 10 (.leaf (2)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (7)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (6)) (.leaf (5))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (4)) (.leaf (7))) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (3))) (.branch 44 (.leaf (0)) (.leaf (5)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (6)) (.leaf (3))) (.branch 51 (.leaf (0)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (7)) (.leaf (5))))))))
  code := certificateD8_1414
  counts := ![(.branch 27 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 44 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 47 (.leaf (14)) (.leaf (15))) (.branch 54 (.leaf (16)) (.branch 57 (.leaf (17)) (.leaf (18))))))),
  (.branch 26 (.branch 12 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 56 (.leaf (-10)) (.leaf (-8))) (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-4)) (.leaf (-2))))),
  (.branch 51 (.leaf (-5)) (.branch 59 (.leaf (-4)) (.leaf (-2)))),
  (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 54 (.branch 51 (.branch 50 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_156_1415 : CycleWitness 8 where
  length := 60
  word := (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (2))) (.branch 10 (.leaf (4)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (2)) (.leaf (4))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (2)) (.leaf (3))) (.branch 40 (.leaf (4)) (.leaf (0)))) (.branch 43 (.branch 42 (.leaf (1)) (.leaf (2))) (.branch 44 (.leaf (0)) (.leaf (3)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (7)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (4))) (.branch 51 (.leaf (0)) (.leaf (1))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (1)))) (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (3)) (.leaf (4))))))))
  code := certificateD8_1415
  counts := ![(.branch 27 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 44 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.branch 41 (.leaf (12)) (.leaf (13))))) (.branch 51 (.branch 47 (.leaf (14)) (.leaf (15))) (.branch 54 (.leaf (16)) (.branch 57 (.leaf (17)) (.leaf (18))))))),
  (.branch 26 (.branch 12 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 35 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 59 (.leaf (8)) (.leaf (9)))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-8)))) (.branch 43 (.branch 38 (.leaf (-9)) (.leaf (-12))) (.branch 58 (.leaf (-13)) (.leaf (-16))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 45 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-52))),
  (.branch 28 (.leaf (0)) (.leaf (-32))),
  (.branch 48 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-6)) (.leaf (-3)))),
  (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))),
  (.branch 59 (.leaf (-16)) (.leaf (-14))),
  (.leaf (-4)),
  (.leaf (0)),
  (.branch 34 (.branch 21 (.branch 14 (.branch 11 (.branch 9 (.leaf (-52)) (.branch 10 (.leaf (-51)) (.leaf (-50)))) (.branch 12 (.leaf (-49)) (.branch 13 (.leaf (-48)) (.leaf (-47))))) (.branch 17 (.branch 15 (.leaf (-46)) (.branch 16 (.leaf (-45)) (.leaf (-44)))) (.branch 19 (.branch 18 (.leaf (-43)) (.leaf (-42))) (.branch 20 (.leaf (-41)) (.leaf (-40)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-39)) (.branch 23 (.leaf (-38)) (.leaf (-37)))) (.branch 25 (.leaf (-36)) (.branch 26 (.leaf (-35)) (.leaf (-34))))) (.branch 30 (.branch 28 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))) (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.leaf (-27))))))) (.branch 47 (.branch 40 (.branch 37 (.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-25)) (.leaf (-24)))) (.branch 38 (.leaf (-23)) (.branch 39 (.leaf (-22)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-20)) (.branch 42 (.leaf (-19)) (.leaf (-18)))) (.branch 45 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 53 (.branch 50 (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11)))) (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8))))) (.branch 56 (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 44 (.branch 36 (.branch 32 (.branch 30 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.leaf (-29)))) (.branch 34 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 35 (.leaf (-26)) (.leaf (-25))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-23))) (.branch 39 (.leaf (-22)) (.leaf (-21)))) (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.leaf (-17)))))) (.branch 52 (.branch 48 (.branch 46 (.branch 45 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-14)) (.leaf (-13)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))) (.branch 58 (.branch 57 (.leaf (-4)) (.leaf (-3))) (.branch 59 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 51 (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10)))) (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7))))) (.branch 57 (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))) (.branch 58 (.leaf (-3)) (.branch 59 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_156 : Fin 16 → CycleWitness 8 := ![witnessD8_156_1400, witnessD8_156_1401, witnessD8_156_1402, witnessD8_156_1403, witnessD8_156_1404, witnessD8_156_1405, witnessD8_156_1406, witnessD8_156_1407, witnessD8_156_1408, witnessD8_156_1409, witnessD8_156_1410, witnessD8_156_1411, witnessD8_156_1412, witnessD8_156_1413, witnessD8_156_1414, witnessD8_156_1415]
end RealPinwheel.FiveSixths


