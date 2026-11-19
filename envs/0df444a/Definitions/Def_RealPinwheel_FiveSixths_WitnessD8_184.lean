-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_184
-- name    : RealPinwheel_FiveSixths_WitnessD8_184
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:33:17.982821+00:00
-- url     : https://prove2.me/theorems/e4e85c38-c42f-4b4e-a121-7abcac1cb1f5
-- title:
--   Exact witness block D8_184
-- statement:
--   These exact witnesses represent words 1893 through 1912 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1893–1912; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_184_1892 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (4)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (7)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (6)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (4))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (7)) (.branch 30 (.leaf (5)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (3)) (.branch 33 (.leaf (1)) (.leaf (4)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (2)) (.leaf (6)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (5)) (.branch 39 (.leaf (0)) (.leaf (1)))) (.branch 41 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (7)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (5)) (.leaf (0))) (.branch 49 (.leaf (3)) (.leaf (4))))))))
  code := certificateD8_1892
  counts := ![(.branch 23 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 26 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-17)) (.leaf (-18)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-16))) (.branch 19 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-38)) (.leaf (-40)))),
  (.branch 12 (.leaf (0)) (.branch 45 (.leaf (-14)) (.leaf (-15))))]
  high := ![(.branch 44 (.branch 27 (.leaf (-17)) (.leaf (-16))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 47 (.branch 34 (.leaf (-18)) (.leaf (-16))) (.branch 48 (.leaf (-12)) (.branch 49 (.leaf (-8)) (.leaf (-4))))),
  (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 33 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 48 (.branch 39 (.leaf (-11)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3)))),
  (.branch 43 (.branch 39 (.branch 21 (.leaf (-40)) (.branch 38 (.leaf (-39)) (.leaf (-36)))) (.branch 41 (.branch 40 (.leaf (-33)) (.leaf (-30))) (.branch 42 (.leaf (-27)) (.leaf (-24))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-18)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-12))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))]
def witnessD8_184_1893 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (6)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (7)) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (2)) (.leaf (5))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 29 (.leaf (6)) (.branch 30 (.leaf (0)) (.leaf (2))))) (.branch 34 (.branch 32 (.leaf (4)) (.branch 33 (.leaf (1)) (.leaf (3)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (7)) (.leaf (5)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (2)) (.branch 39 (.leaf (0)) (.leaf (1)))) (.branch 41 (.leaf (4)) (.branch 42 (.leaf (3)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (6)) (.branch 45 (.leaf (2)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (4))) (.branch 49 (.leaf (3)) (.leaf (5))))))))
  code := certificateD8_1893
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.leaf (7))))),
  (.branch 28 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-19)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-17)) (.leaf (-18)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-25)) (.leaf (-32)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-7))) (.branch 20 (.leaf (-8)) (.branch 34 (.leaf (-9)) (.leaf (-11))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (-3))) (.branch 48 (.leaf (-5)) (.leaf (-6)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.branch 44 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-13)) (.leaf (-15))))]
  high := ![(.branch 48 (.branch 31 (.leaf (-20)) (.leaf (-18))) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 47 (.branch 34 (.leaf (-18)) (.leaf (-16))) (.branch 48 (.leaf (-12)) (.branch 49 (.leaf (-8)) (.leaf (-4))))),
  (.branch 47 (.branch 10 (.leaf (-32)) (.branch 46 (.leaf (-31)) (.leaf (-25)))) (.branch 48 (.leaf (-19)) (.branch 49 (.leaf (-13)) (.leaf (-7))))),
  (.branch 35 (.leaf (-11)) (.leaf (-7))),
  (.branch 49 (.leaf (-6)) (.leaf (-4))),
  (.branch 38 (.leaf (-1)) (.leaf (0))),
  (.branch 47 (.branch 45 (.leaf (-7)) (.branch 46 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2))))),
  (.branch 43 (.branch 39 (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))) (.branch 41 (.branch 40 (.leaf (-12)) (.leaf (-11))) (.branch 42 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.leaf (-2))))))]
def witnessD8_184_1894 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (3)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (7)) (.leaf (0)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (1))) (.branch 24 (.leaf (4)) (.leaf (5))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (7))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (4)) (.leaf (2)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (3)) (.leaf (5)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (1)) (.branch 39 (.leaf (6)) (.leaf (0)))) (.branch 41 (.leaf (4)) (.branch 42 (.leaf (2)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (3)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (7)) (.leaf (2))) (.branch 49 (.leaf (4)) (.leaf (5))))))))
  code := certificateD8_1894
  counts := ![(.branch 21 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))) (.branch 35 (.branch 29 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 32 (.leaf (9)) (.leaf (10)))) (.branch 43 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 46 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 7 (.leaf (-4)) (.leaf (-5)))) (.branch 32 (.branch 21 (.leaf (-6)) (.leaf (-7))) (.branch 35 (.leaf (-8)) (.branch 46 (.leaf (-9)) (.leaf (-10)))))),
  (.branch 23 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-16)) (.leaf (-17)))) (.branch 30 (.leaf (-19)) (.branch 44 (.leaf (-20)) (.leaf (-22))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 48 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (-1))) (.branch 24 (.leaf (-2)) (.leaf (-3)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (-32)) (.leaf (-34)))),
  (.branch 14 (.leaf (0)) (.branch 47 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.leaf (-7)))),
  (.branch 47 (.branch 45 (.leaf (-22)) (.branch 46 (.leaf (-19)) (.leaf (-16)))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-10)) (.leaf (-7))))),
  (.branch 49 (.leaf (-10)) (.leaf (-7))),
  (.branch 47 (.branch 37 (.leaf (-17)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 38 (.leaf (-1)) (.leaf (0))),
  (.branch 44 (.branch 41 (.branch 23 (.leaf (-34)) (.branch 40 (.leaf (-33)) (.leaf (-30)))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-24)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))]
def witnessD8_184_1895 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (5)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (1)) (.leaf (3)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (6)) (.leaf (2))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (4)) (.branch 33 (.leaf (2)) (.leaf (0)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (5)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (2)) (.branch 39 (.leaf (1)) (.leaf (3)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (1))))) (.branch 46 (.branch 44 (.leaf (4)) (.branch 45 (.leaf (0)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_1895
  counts := ![(.branch 23 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 45 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 48 (.leaf (13)) (.leaf (14)))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 26 (.leaf (-13)) (.leaf (-14)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))) (.branch 18 (.branch 14 (.leaf (-15)) (.leaf (-16))) (.branch 22 (.leaf (-17)) (.leaf (-18))))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-19)) (.leaf (-20)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-11)) (.leaf (-12)))),
  (.branch 11 (.leaf (0)) (.leaf (-14))),
  (.branch 24 (.leaf (0)) (.leaf (-26))),
  (.branch 49 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 38 (.branch 27 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 48 (.leaf (-18)) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 34 (.leaf (-2)) (.leaf (0))),
  (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-18))) (.branch 43 (.leaf (-16)) (.branch 44 (.leaf (-14)) (.leaf (-12))))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-10)) (.leaf (-8)))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 43 (.branch 39 (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))) (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.leaf (-8))))) (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 30 (.branch 27 (.branch 25 (.leaf (-26)) (.branch 26 (.leaf (-25)) (.leaf (-24)))) (.branch 28 (.leaf (-23)) (.branch 29 (.leaf (-22)) (.leaf (-21))))) (.branch 33 (.branch 31 (.leaf (-20)) (.branch 32 (.leaf (-19)) (.leaf (-18)))) (.branch 35 (.branch 34 (.leaf (-17)) (.leaf (-16))) (.branch 36 (.leaf (-15)) (.leaf (-14)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-12)) (.leaf (-11)))) (.branch 41 (.leaf (-10)) (.branch 42 (.leaf (-9)) (.leaf (-8))))) (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD8_184_1896 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (1)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (4))) (.branch 24 (.leaf (2)) (.leaf (0))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (6)) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (2)) (.leaf (4))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (3)))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (0)) (.leaf (1)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (4)) (.branch 39 (.leaf (2)) (.leaf (3)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (7))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (4))) (.branch 49 (.leaf (0)) (.leaf (2))))))))
  code := certificateD8_1896
  counts := ![(.branch 25 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 28 (.leaf (7)) (.branch 33 (.leaf (8)) (.leaf (9)))) (.branch 44 (.branch 41 (.leaf (10)) (.leaf (11))) (.branch 49 (.leaf (12)) (.leaf (13)))))),
  (.branch 22 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 42 (.leaf (9)) (.branch 47 (.leaf (10)) (.leaf (11)))))),
  (.branch 30 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 45 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-20)) (.leaf (-25)))) (.branch 19 (.leaf (-31)) (.branch 22 (.leaf (-37)) (.leaf (-50))))),
  (.branch 39 (.leaf (0)) (.leaf (-8))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-4)) (.leaf (-6)))) (.branch 40 (.branch 34 (.leaf (-7)) (.leaf (-8))) (.branch 46 (.leaf (-9)) (.leaf (-10))))),
  (.branch 4 (.leaf (0)) (.branch 38 (.leaf (-5)) (.leaf (-7)))),
  (.branch 10 (.leaf (0)) (.leaf (-40))),
  (.branch 26 (.leaf (0)) (.leaf (-24))),
  (.branch 43 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 45 (.leaf (-4)) (.leaf (-3))),
  (.branch 38 (.branch 28 (.branch 23 (.leaf (-50)) (.leaf (-49))) (.branch 33 (.leaf (-48)) (.leaf (-47)))) (.branch 48 (.branch 43 (.leaf (-46)) (.leaf (-45))) (.branch 49 (.leaf (-38)) (.leaf (-31))))),
  (.branch 46 (.branch 40 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-2)) (.leaf (0)))),
  (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.leaf (-7)))),
  (.branch 39 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))),
  (.branch 30 (.branch 20 (.branch 15 (.branch 12 (.branch 11 (.leaf (-40)) (.leaf (-39))) (.branch 13 (.leaf (-38)) (.branch 14 (.leaf (-37)) (.leaf (-36))))) (.branch 17 (.branch 16 (.leaf (-35)) (.leaf (-34))) (.branch 18 (.leaf (-33)) (.branch 19 (.leaf (-32)) (.leaf (-31)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-30)) (.leaf (-29))) (.branch 23 (.leaf (-28)) (.branch 24 (.leaf (-27)) (.leaf (-26))))) (.branch 27 (.branch 26 (.leaf (-25)) (.leaf (-24))) (.branch 28 (.leaf (-23)) (.branch 29 (.leaf (-22)) (.leaf (-21))))))) (.branch 40 (.branch 35 (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-19))) (.branch 33 (.leaf (-18)) (.branch 34 (.leaf (-17)) (.leaf (-16))))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-14))) (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-12)) (.leaf (-11)))))) (.branch 45 (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-8)) (.branch 44 (.leaf (-7)) (.leaf (-6))))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 38 (.branch 32 (.branch 29 (.branch 27 (.leaf (-24)) (.branch 28 (.leaf (-23)) (.leaf (-22)))) (.branch 30 (.leaf (-21)) (.branch 31 (.leaf (-20)) (.leaf (-19))))) (.branch 35 (.branch 33 (.leaf (-18)) (.branch 34 (.leaf (-17)) (.leaf (-16)))) (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-14)) (.leaf (-13)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (-12)) (.branch 40 (.leaf (-11)) (.leaf (-10)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_184_1897 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (7)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (3)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (6))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (1))) (.branch 24 (.leaf (5)) (.leaf (7))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (1)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (6)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (5)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (1)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (4)) (.leaf (7))))) (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (0)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (2))) (.branch 49 (.leaf (5)) (.leaf (6))))))))
  code := certificateD8_1897
  counts := ![(.branch 20 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 26 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 41 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 40 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 48 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 34 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 23 (.leaf (-5)) (.branch 40 (.leaf (-7)) (.leaf (-8))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))) (.branch 32 (.leaf (-3)) (.branch 48 (.leaf (-4)) (.leaf (-6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-10)))) (.branch 33 (.leaf (-11)) (.branch 39 (.leaf (-12)) (.leaf (-13))))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))),
  (.branch 48 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-5)))),
  (.branch 49 (.leaf (-6)) (.leaf (-5))),
  (.branch 47 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 48 (.leaf (-10)) (.branch 49 (.leaf (-8)) (.leaf (-6))))),
  (.branch 45 (.branch 43 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-14)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (-2)),
  (.leaf (0)),
  (.branch 46 (.branch 44 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.leaf (-2)))))]
def witnessD8_184_1898 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (7)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (2)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (5)) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (3))) (.branch 24 (.leaf (6)) (.leaf (1))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (1)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (5)) (.branch 33 (.leaf (2)) (.leaf (3)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (7)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (4)) (.branch 39 (.leaf (2)) (.leaf (0)))) (.branch 41 (.leaf (3)) (.branch 42 (.leaf (1)) (.leaf (2))))) (.branch 46 (.branch 44 (.leaf (5)) (.branch 45 (.leaf (4)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (3))) (.branch 49 (.leaf (6)) (.leaf (2))))))))
  code := certificateD8_1898
  counts := ![(.branch 21 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 26 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 46 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 39 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 43 (.leaf (7)) (.branch 50 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-4)) (.leaf (-5)))),
  (.branch 18 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 35 (.leaf (-6)) (.leaf (-7)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 27 (.leaf (-2)) (.branch 43 (.leaf (-3)) (.leaf (-5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 28 (.leaf (-8)) (.branch 34 (.leaf (-9)) (.leaf (-10))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (-9))) (.branch 45 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-11)) (.leaf (-12)))),
  (.branch 24 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 47 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))),
  (.branch 48 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))),
  (.branch 46 (.branch 44 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (-3)))) (.branch 47 (.leaf (-2)) (.branch 48 (.leaf (-1)) (.leaf (0))))),
  (.branch 42 (.branch 35 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.leaf (-6)))),
  (.branch 47 (.branch 46 (.leaf (-12)) (.leaf (-10))) (.branch 48 (.leaf (-8)) (.branch 49 (.leaf (-6)) (.leaf (-4))))),
  (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-10)) (.leaf (-8)))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-1)),
  (.branch 43 (.branch 40 (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-12)) (.leaf (-11)))) (.branch 41 (.leaf (-10)) (.branch 42 (.leaf (-9)) (.leaf (-8))))) (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_184_1899 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (6)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (3)) (.leaf (7)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (4)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (5)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (4)) (.leaf (7))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (1)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (4)) (.branch 33 (.leaf (6)) (.leaf (2)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (3)) (.leaf (7)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (4)))) (.branch 41 (.leaf (2)) (.branch 42 (.leaf (5)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (3)) (.leaf (6)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (2))) (.branch 49 (.leaf (4)) (.leaf (7))))))))
  code := certificateD8_1899
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-19))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-31)) (.leaf (-32)))) (.branch 30 (.branch 23 (.leaf (-33)) (.leaf (-34))) (.branch 44 (.leaf (-35)) (.leaf (-37))))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-13)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 48 (.branch 27 (.leaf (-19)) (.leaf (-18))) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 47 (.branch 45 (.leaf (-37)) (.branch 46 (.leaf (-31)) (.leaf (-25)))) (.branch 48 (.leaf (-19)) (.branch 49 (.leaf (-13)) (.leaf (-7))))),
  (.branch 20 (.leaf (-15)) (.branch 49 (.leaf (-13)) (.leaf (-7)))),
  (.branch 47 (.branch 37 (.leaf (-17)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 41 (.leaf (-5)) (.leaf (-3))),
  (.branch 45 (.branch 43 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-14)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 47 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 38 (.leaf (-1)) (.leaf (0)))]
def witnessD8_184_1900 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (3)) (.leaf (7)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (4)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (6)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (4))) (.branch 24 (.leaf (3)) (.leaf (1))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (5)) (.leaf (2)))) (.branch 29 (.leaf (7)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (4)) (.branch 33 (.leaf (3)) (.leaf (0)))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (1)) (.leaf (6)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (4)))) (.branch 41 (.leaf (1)) (.branch 42 (.leaf (2)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (5)) (.branch 45 (.leaf (7)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (3))) (.branch 49 (.leaf (4)) (.leaf (2))))))))
  code := certificateD8_1900
  counts := ![(.branch 21 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 41 (.leaf (7)) (.branch 46 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-16)) (.leaf (-17)))) (.branch 17 (.leaf (-18)) (.branch 21 (.leaf (-20)) (.leaf (-21))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-15))) (.branch 41 (.leaf (-18)) (.branch 46 (.leaf (-20)) (.leaf (-23))))),
  (.branch 28 (.branch 22 (.leaf (0)) (.leaf (-3))) (.branch 35 (.leaf (-8)) (.branch 42 (.leaf (-10)) (.leaf (-12))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 24 (.leaf (-6)) (.branch 39 (.leaf (-8)) (.leaf (-9))))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 10 (.leaf (0)) (.leaf (-20))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-38)) (.leaf (-40)))),
  (.branch 12 (.leaf (0)) (.branch 45 (.leaf (-14)) (.leaf (-15))))]
  high := ![(.branch 39 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-7))))),
  (.branch 48 (.branch 47 (.leaf (-23)) (.leaf (-19))) (.branch 49 (.leaf (-15)) (.leaf (-11)))),
  (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-9))) (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-3)) (.leaf (0))))),
  (.branch 40 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7)))),
  (.branch 24 (.branch 7 (.leaf (-12)) (.leaf (-11))) (.branch 41 (.leaf (-10)) (.leaf (-7)))),
  (.branch 46 (.branch 28 (.branch 11 (.leaf (-20)) (.leaf (-19))) (.branch 45 (.leaf (-18)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 43 (.branch 39 (.branch 21 (.leaf (-40)) (.branch 38 (.leaf (-39)) (.leaf (-36)))) (.branch 41 (.branch 40 (.leaf (-33)) (.leaf (-30))) (.branch 42 (.leaf (-27)) (.leaf (-24))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-18)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-12))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))]
def witnessD8_184_1901 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (5)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (2)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (1)) (.leaf (4)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (7)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (6)) (.leaf (3))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (4)))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (7)) (.branch 33 (.leaf (0)) (.leaf (5)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (2)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (3)) (.branch 39 (.leaf (1)) (.leaf (4)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (6)) (.leaf (1))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (5)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (7)) (.leaf (3))))))))
  code := certificateD8_1901
  counts := ![(.branch 22 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 22 (.leaf (-14)) (.branch 47 (.leaf (-16)) (.leaf (-17))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))) (.branch 14 (.leaf (-15)) (.branch 18 (.leaf (-16)) (.leaf (-17))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-9))) (.branch 36 (.leaf (-12)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-19)) (.leaf (-20)))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 32 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 44 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 47 (.branch 37 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 48 (.leaf (-8)) (.branch 49 (.leaf (-6)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 45 (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-18))) (.branch 43 (.leaf (-16)) (.branch 44 (.leaf (-14)) (.leaf (-12))))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-6))) (.branch 49 (.leaf (-4)) (.leaf (-2)))),
  (.branch 45 (.branch 43 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.leaf (-7)))) (.branch 47 (.branch 46 (.leaf (-6)) (.leaf (-5))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2)))))),
  (.leaf (-2))]
def witnessD8_184_1902 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (6)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (7)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (1)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (5)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (0))) (.branch 24 (.leaf (7)) (.leaf (1))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (2)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (5)) (.branch 33 (.leaf (0)) (.leaf (6)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (7)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (2)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (4)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (5)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (6)) (.leaf (0))) (.branch 49 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_1902
  counts := ![(.branch 23 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 36 (.branch 28 (.branch 26 (.leaf (10)) (.leaf (11))) (.branch 31 (.leaf (12)) (.branch 33 (.leaf (13)) (.leaf (14))))) (.branch 43 (.branch 38 (.leaf (15)) (.branch 41 (.leaf (16)) (.leaf (17)))) (.branch 46 (.leaf (18)) (.branch 48 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 45 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.branch 14 (.leaf (-21)) (.leaf (-22)))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-11)) (.leaf (-12)))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 49 (.leaf (-4)) (.leaf (-2))),
  (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 44 (.branch 41 (.branch 40 (.leaf (-22)) (.leaf (-20))) (.branch 42 (.leaf (-18)) (.branch 43 (.leaf (-16)) (.leaf (-14))))) (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-10)) (.leaf (-8)))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 45 (.branch 43 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-14)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-10)) (.leaf (-8)))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 48 (.branch 35 (.leaf (-7)) (.leaf (-6))) (.branch 49 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-2))]
def witnessD8_184_1903 : CycleWitness 8 where
  length := 49
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (7)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (6)) (.leaf (0))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (5)) (.branch 29 (.leaf (0)) (.leaf (3))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (7)) (.leaf (0)))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (4)))))) (.branch 43 (.branch 40 (.branch 37 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (6)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (3)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (5)) (.branch 45 (.leaf (0)) (.leaf (2)))) (.branch 47 (.leaf (1)) (.branch 48 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_1903
  counts := ![(.branch 23 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 16 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))) (.branch 19 (.leaf (9)) (.branch 21 (.leaf (10)) (.leaf (11)))))) (.branch 35 (.branch 29 (.branch 25 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14)))) (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17))))) (.branch 41 (.branch 38 (.leaf (18)) (.branch 39 (.leaf (19)) (.leaf (20)))) (.branch 45 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 48 (.leaf (23)) (.leaf (24))))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 14 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 4 (.leaf (-22)) (.branch 6 (.leaf (-23)) (.leaf (-24))))) (.branch 41 (.branch 16 (.leaf (-28)) (.branch 39 (.leaf (-29)) (.leaf (-30)))) (.branch 43 (.leaf (-31)) (.branch 45 (.leaf (-32)) (.leaf (-33)))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (-2))) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (-9))) (.branch 34 (.leaf (-10)) (.branch 46 (.leaf (-11)) (.leaf (-12))))),
  (.branch 5 (.leaf (0)) (.leaf (-29))),
  (.branch 3 (.leaf (0)) (.leaf (-40))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (-13))) (.branch 44 (.leaf (-14)) (.leaf (-15)))),
  (.branch 7 (.leaf (0)) (.leaf (-28))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 46 (.leaf (-33)) (.leaf (-24))),
  (.branch 27 (.leaf (-4)) (.branch 48 (.leaf (-3)) (.leaf (-2)))),
  (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-8)) (.leaf (-4)))),
  (.branch 45 (.branch 43 (.branch 6 (.leaf (-29)) (.leaf (-28))) (.branch 44 (.leaf (-24)) (.leaf (-20)))) (.branch 47 (.branch 46 (.leaf (-16)) (.leaf (-12))) (.branch 48 (.leaf (-8)) (.leaf (-4))))),
  (.branch 42 (.branch 38 (.branch 4 (.leaf (-40)) (.branch 37 (.leaf (-39)) (.leaf (-36)))) (.branch 40 (.branch 39 (.leaf (-33)) (.leaf (-30))) (.branch 41 (.leaf (-27)) (.leaf (-24))))) (.branch 45 (.branch 43 (.leaf (-21)) (.branch 44 (.leaf (-18)) (.leaf (-15)))) (.branch 47 (.branch 46 (.leaf (-12)) (.leaf (-9))) (.branch 48 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 46 (.branch 45 (.leaf (-15)) (.leaf (-12))) (.branch 47 (.leaf (-9)) (.branch 48 (.leaf (-6)) (.leaf (-3))))),
  (.branch 44 (.branch 41 (.branch 8 (.leaf (-28)) (.leaf (-27))) (.branch 42 (.leaf (-24)) (.branch 43 (.leaf (-21)) (.leaf (-18))))) (.branch 46 (.branch 45 (.leaf (-15)) (.leaf (-12))) (.branch 47 (.leaf (-9)) (.branch 48 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 16 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (0))))]
def witnessD8_184_1904 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (5))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.leaf (6)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (4)))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (0)) (.leaf (5))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (7)))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (2))) (.branch 47 (.leaf (0)) (.leaf (4)))))))
  code := certificateD8_1904
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.leaf (7))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (8)) (.leaf (9))) (.branch 16 (.leaf (10)) (.leaf (11)))) (.branch 20 (.branch 19 (.leaf (12)) (.leaf (13))) (.branch 22 (.leaf (14)) (.leaf (15)))))) (.branch 35 (.branch 29 (.branch 26 (.branch 25 (.leaf (16)) (.leaf (17))) (.branch 28 (.leaf (18)) (.leaf (19)))) (.branch 32 (.branch 31 (.leaf (20)) (.leaf (21))) (.branch 34 (.leaf (22)) (.leaf (23))))) (.branch 41 (.branch 38 (.branch 37 (.leaf (24)) (.leaf (25))) (.branch 40 (.leaf (26)) (.leaf (27)))) (.branch 44 (.branch 43 (.leaf (28)) (.leaf (29))) (.branch 46 (.leaf (30)) (.branch 47 (.leaf (31)) (.leaf (32)))))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-18))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-30))),
  (.branch 42 (.leaf (0)) (.leaf (-6)))]
  high := ![(.leaf (-2)),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 34 (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0)),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 25 (.branch 21 (.branch 19 (.leaf (-30)) (.branch 20 (.leaf (-29)) (.leaf (-28)))) (.branch 23 (.branch 22 (.leaf (-27)) (.leaf (-26))) (.branch 24 (.leaf (-25)) (.leaf (-24))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-23)) (.leaf (-22))) (.branch 28 (.leaf (-21)) (.leaf (-20)))) (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))))) (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_184_1905 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (4))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (6)) (.branch 23 (.leaf (0)) (.leaf (3))))))) (.branch 36 (.branch 31 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (0))))) (.branch 33 (.branch 32 (.leaf (4)) (.leaf (0))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (0)) (.leaf (1)))))) (.branch 43 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (0))))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (0))) (.branch 46 (.leaf (7)) (.branch 47 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_1905
  counts := ![(.branch 23 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 16 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))) (.branch 19 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 21 (.leaf (12)) (.leaf (13)))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (14)) (.branch 26 (.leaf (15)) (.leaf (16)))) (.branch 31 (.branch 30 (.leaf (17)) (.leaf (18))) (.branch 33 (.leaf (19)) (.leaf (20))))) (.branch 42 (.branch 38 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 40 (.leaf (23)) (.leaf (24)))) (.branch 45 (.branch 43 (.leaf (25)) (.leaf (26))) (.branch 47 (.leaf (27)) (.leaf (28))))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 46 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.branch 39 (.leaf (-8)) (.leaf (-9)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-14))),
  (.branch 22 (.leaf (0)) (.leaf (-26))),
  (.branch 46 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 44 (.leaf (-11)) (.branch 46 (.leaf (-9)) (.leaf (-7)))),
  (.branch 45 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-1)) (.leaf (0))),
  (.branch 41 (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.branch 28 (.branch 25 (.branch 23 (.leaf (-26)) (.branch 24 (.leaf (-25)) (.leaf (-24)))) (.branch 26 (.leaf (-23)) (.branch 27 (.leaf (-22)) (.leaf (-21))))) (.branch 31 (.branch 29 (.leaf (-20)) (.branch 30 (.leaf (-19)) (.leaf (-18)))) (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))))) (.branch 41 (.branch 38 (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))) (.branch 39 (.leaf (-10)) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_184_1906 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 20 (.leaf (5)) (.leaf (0))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (3))))))) (.branch 36 (.branch 31 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (0))))) (.branch 33 (.branch 32 (.leaf (6)) (.leaf (0))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (3)))))) (.branch 43 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (0))))) (.branch 45 (.branch 44 (.leaf (7)) (.leaf (0))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_1906
  counts := ![(.branch 23 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 16 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))) (.branch 19 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 21 (.leaf (12)) (.leaf (13)))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (14)) (.branch 26 (.leaf (15)) (.leaf (16)))) (.branch 31 (.branch 30 (.leaf (17)) (.leaf (18))) (.branch 33 (.leaf (19)) (.leaf (20))))) (.branch 42 (.branch 38 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 40 (.leaf (23)) (.leaf (24)))) (.branch 45 (.branch 43 (.leaf (25)) (.leaf (26))) (.branch 47 (.leaf (27)) (.leaf (28))))))),
  (.branch 22 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-40))),
  (.branch 20 (.leaf (0)) (.leaf (-28))),
  (.branch 32 (.leaf (0)) (.leaf (-16))),
  (.branch 44 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 44 (.leaf (-11)) (.branch 46 (.leaf (-9)) (.leaf (-7)))),
  (.branch 40 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 28 (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-40)) (.leaf (-39))) (.branch 11 (.leaf (-38)) (.branch 12 (.leaf (-37)) (.leaf (-36))))) (.branch 15 (.branch 14 (.leaf (-35)) (.leaf (-34))) (.branch 16 (.leaf (-33)) (.branch 17 (.leaf (-32)) (.leaf (-31)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-30)) (.leaf (-29))) (.branch 21 (.leaf (-28)) (.branch 22 (.leaf (-27)) (.leaf (-26))))) (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.branch 27 (.leaf (-22)) (.leaf (-21))))))) (.branch 38 (.branch 33 (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 34 (.branch 27 (.branch 23 (.branch 21 (.leaf (-28)) (.branch 22 (.leaf (-27)) (.leaf (-26)))) (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.leaf (-22))))) (.branch 30 (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19)))) (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))))) (.branch 41 (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_184_1907 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (0))) (.branch 9 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (0))) (.branch 21 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (6))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (0))))) (.branch 32 (.branch 31 (.leaf (4)) (.leaf (0))) (.branch 33 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (3)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (0))))) (.branch 44 (.branch 43 (.leaf (5)) (.leaf (0))) (.branch 45 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_1907
  counts := ![(.branch 23 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 16 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))) (.branch 20 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 22 (.leaf (12)) (.leaf (13)))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (14)) (.branch 26 (.leaf (15)) (.leaf (16)))) (.branch 32 (.branch 30 (.leaf (17)) (.leaf (18))) (.branch 34 (.leaf (19)) (.leaf (20))))) (.branch 42 (.branch 38 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 40 (.leaf (23)) (.leaf (24)))) (.branch 46 (.branch 44 (.leaf (25)) (.leaf (26))) (.branch 47 (.leaf (27)) (.leaf (28))))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 26 (.leaf (-7)) (.branch 38 (.leaf (-8)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.branch 7 (.leaf (0)) (.leaf (-17))),
  (.branch 19 (.leaf (0)) (.leaf (-5))),
  (.branch 24 (.leaf (0)) (.leaf (-24))),
  (.leaf (0))]
  high := ![(.branch 39 (.leaf (-9)) (.leaf (-8))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 37 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.leaf (-10))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))) (.branch 33 (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_184_1908 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (4)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (1))))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (7)) (.leaf (1))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (1))))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (5)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (3)) (.leaf (1))))) (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (6)) (.leaf (1))))))))
  code := certificateD8_1908
  counts := ![(.branch 22 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 16 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))) (.branch 19 (.leaf (9)) (.branch 20 (.leaf (10)) (.leaf (11)))))) (.branch 34 (.branch 28 (.branch 25 (.leaf (12)) (.branch 26 (.leaf (13)) (.leaf (14)))) (.branch 31 (.leaf (15)) (.branch 32 (.leaf (16)) (.leaf (17))))) (.branch 40 (.branch 37 (.leaf (18)) (.branch 38 (.leaf (19)) (.leaf (20)))) (.branch 44 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 46 (.leaf (23)) (.leaf (24))))))),
  (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 42 (.branch 39 (.leaf (12)) (.leaf (13))) (.branch 45 (.leaf (14)) (.branch 48 (.leaf (15)) (.leaf (16))))))),
  (.branch 5 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.branch 17 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-37))),
  (.branch 35 (.leaf (0)) (.leaf (-13))),
  (.branch 47 (.leaf (0)) (.leaf (-1))),
  (.branch 23 (.leaf (0)) (.leaf (-25)))]
  high := ![(.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 38 (.branch 33 (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 20 (.branch 15 (.branch 13 (.branch 12 (.leaf (-37)) (.leaf (-36))) (.branch 14 (.leaf (-35)) (.leaf (-34)))) (.branch 17 (.branch 16 (.leaf (-33)) (.leaf (-32))) (.branch 18 (.leaf (-31)) (.branch 19 (.leaf (-30)) (.leaf (-29)))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-28)) (.leaf (-27))) (.branch 23 (.leaf (-26)) (.leaf (-25)))) (.branch 26 (.branch 25 (.leaf (-24)) (.leaf (-23))) (.branch 27 (.leaf (-22)) (.branch 28 (.leaf (-21)) (.leaf (-20))))))) (.branch 38 (.branch 33 (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 38 (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))) (.branch 39 (.leaf (-10)) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 35 (.branch 29 (.branch 26 (.branch 24 (.leaf (-25)) (.branch 25 (.leaf (-24)) (.leaf (-23)))) (.branch 27 (.leaf (-22)) (.branch 28 (.leaf (-21)) (.leaf (-20))))) (.branch 32 (.branch 30 (.leaf (-19)) (.branch 31 (.leaf (-18)) (.leaf (-17)))) (.branch 33 (.leaf (-16)) (.branch 34 (.leaf (-15)) (.leaf (-14)))))) (.branch 41 (.branch 38 (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))) (.branch 39 (.leaf (-10)) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_184_1909 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (4)) (.leaf (0)))))) (.branch 18 (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (2))))))) (.branch 36 (.branch 29 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (4)) (.branch 28 (.leaf (0)) (.leaf (1))))) (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (6)) (.leaf (1)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (0)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (4)) (.branch 44 (.leaf (0)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (7)) (.leaf (1))))))))
  code := certificateD8_1909
  counts := ![(.branch 23 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 12 (.leaf (5)) (.branch 14 (.leaf (6)) (.leaf (7)))) (.branch 18 (.leaf (8)) (.branch 20 (.leaf (9)) (.leaf (10)))))) (.branch 34 (.branch 28 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.branch 33 (.leaf (14)) (.leaf (15))))) (.branch 41 (.branch 36 (.leaf (16)) (.branch 39 (.leaf (17)) (.leaf (18)))) (.branch 44 (.leaf (19)) (.branch 46 (.leaf (20)) (.leaf (21))))))),
  (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.leaf (15)))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 18 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 4 (.leaf (-14)) (.leaf (-16)))) (.branch 34 (.branch 20 (.leaf (-18)) (.leaf (-20))) (.branch 36 (.leaf (-22)) (.leaf (-24))))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 15 (.leaf (0)) (.leaf (-33))),
  (.branch 31 (.leaf (0)) (.leaf (-17))),
  (.branch 47 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 42 (.branch 37 (.leaf (-24)) (.leaf (-23))) (.branch 47 (.leaf (-22)) (.leaf (-17)))),
  (.branch 39 (.leaf (-2)) (.leaf (0))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (-33)) (.leaf (-32))) (.branch 18 (.leaf (-31)) (.leaf (-30)))) (.branch 21 (.branch 20 (.leaf (-29)) (.leaf (-28))) (.branch 22 (.leaf (-27)) (.leaf (-26))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 29 (.branch 28 (.leaf (-21)) (.leaf (-20))) (.branch 30 (.leaf (-19)) (.leaf (-18)))))) (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 37 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.leaf (-10))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 37 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.leaf (-10))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD8_184_1910 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (6)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (4))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (5)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (3)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (4)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (7)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (3)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (4))))))))
  code := certificateD8_1910
  counts := ![(.branch 22 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 16 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))) (.branch 18 (.leaf (9)) (.branch 20 (.leaf (10)) (.leaf (11)))))) (.branch 34 (.branch 28 (.branch 25 (.leaf (12)) (.branch 26 (.leaf (13)) (.leaf (14)))) (.branch 30 (.leaf (15)) (.branch 32 (.leaf (16)) (.leaf (17))))) (.branch 40 (.branch 37 (.leaf (18)) (.branch 38 (.leaf (19)) (.leaf (20)))) (.branch 44 (.branch 42 (.leaf (21)) (.leaf (22))) (.branch 46 (.leaf (23)) (.leaf (24))))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.branch 17 (.leaf (0)) (.leaf (-31))),
  (.branch 41 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 38 (.branch 33 (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 24 (.branch 20 (.branch 18 (.leaf (-31)) (.branch 19 (.leaf (-30)) (.leaf (-29)))) (.branch 22 (.branch 21 (.leaf (-28)) (.leaf (-27))) (.branch 23 (.leaf (-26)) (.leaf (-25))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-24)) (.leaf (-23))) (.branch 27 (.leaf (-22)) (.leaf (-21)))) (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.leaf (-17)))))) (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_184_1911 : CycleWitness 8 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 7 (.leaf (3)) (.leaf (0))) (.branch 9 (.leaf (6)) (.branch 10 (.leaf (1)) (.leaf (0)))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (1)) (.leaf (4))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (5)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 32 (.branch 31 (.leaf (4)) (.leaf (0))) (.branch 33 (.leaf (7)) (.branch 34 (.leaf (1)) (.leaf (0)))))) (.branch 41 (.branch 38 (.branch 37 (.leaf (1)) (.leaf (3))) (.branch 39 (.leaf (0)) (.branch 40 (.leaf (2)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (5)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (1))))))))
  code := certificateD8_1911
  counts := ![(.branch 22 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 19 (.leaf (8)) (.leaf (9)))))) (.branch 35 (.branch 26 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 42 (.branch 36 (.leaf (15)) (.branch 39 (.leaf (16)) (.leaf (17)))) (.branch 43 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20))))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 48 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 19 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 12 (.leaf (-10)) (.leaf (-12)))) (.branch 36 (.branch 26 (.leaf (-15)) (.leaf (-18))) (.branch 43 (.leaf (-20)) (.leaf (-23))))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 7 (.leaf (0)) (.branch 38 (.leaf (-9)) (.leaf (-10)))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 21 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-39))),
  (.branch 33 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 44 (.leaf (-23)) (.branch 47 (.leaf (-22)) (.leaf (-19)))),
  (.branch 38 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 45 (.leaf (-4)) (.leaf (0)))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 18 (.branch 13 (.branch 11 (.branch 10 (.leaf (-39)) (.leaf (-38))) (.branch 12 (.leaf (-37)) (.leaf (-36)))) (.branch 15 (.branch 14 (.leaf (-35)) (.leaf (-34))) (.branch 16 (.leaf (-33)) (.branch 17 (.leaf (-32)) (.leaf (-31)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-30)) (.leaf (-29))) (.branch 21 (.leaf (-28)) (.branch 22 (.leaf (-27)) (.leaf (-26))))) (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.branch 27 (.leaf (-22)) (.leaf (-21))))))) (.branch 38 (.branch 33 (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_184 : Fin 20 → CycleWitness 8 := ![witnessD8_184_1892, witnessD8_184_1893, witnessD8_184_1894, witnessD8_184_1895, witnessD8_184_1896, witnessD8_184_1897, witnessD8_184_1898, witnessD8_184_1899, witnessD8_184_1900, witnessD8_184_1901, witnessD8_184_1902, witnessD8_184_1903, witnessD8_184_1904, witnessD8_184_1905, witnessD8_184_1906, witnessD8_184_1907, witnessD8_184_1908, witnessD8_184_1909, witnessD8_184_1910, witnessD8_184_1911]
end RealPinwheel.FiveSixths


